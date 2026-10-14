use std::{
    cmp,
    ffi::OsString,
    fmt, iter,
    num::ParseIntError,
    str::FromStr,
    time::{Duration, Instant},
};

use clap::{Arg, ArgAction, ArgMatches, Command, value_parser};
use ff::Field;
use group::{Curve, Group};
use halo2_proofs::{arithmetic::best_multiexp, pasta::pallas};

struct Estimator {
    /// Scalars for estimating multiexp performance.
    multiexp_scalars: Vec<pallas::Scalar>,
    /// Bases for estimating multiexp performance.
    multiexp_bases: Vec<pallas::Affine>,
}

impl fmt::Debug for Estimator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Estimator")
    }
}

impl Estimator {
    fn random(k: usize) -> Self {
        let max_size = 1 << (k + 1);
        let mut rng = rand::rng();

        Estimator {
            multiexp_scalars: (0..max_size)
                .map(|_| pallas::Scalar::random(&mut rng))
                .collect(),
            multiexp_bases: (0..max_size)
                .map(|_| pallas::Point::random(&mut rng).to_affine())
                .collect(),
        }
    }

    fn multiexp(&self, size: usize) -> Duration {
        let start = Instant::now();
        best_multiexp(&self.multiexp_scalars[..size], &self.multiexp_bases[..size]);
        Instant::now().duration_since(start)
    }
}

#[derive(Debug)]
struct CostOptions {
    advice: Vec<Poly>,
    instance: Vec<Poly>,
    fixed: Vec<Poly>,
    gate_degree: usize,
    lookup: Vec<Lookup>,
    permutation: Vec<Permutation>,
    k: usize,
}

impl CostOptions {
    fn command() -> Command {
        // Option values are taken verbatim, so rotation lists such as `-1,0`
        // are not mistaken for flags. Repeating a single-value option keeps
        // the last value.
        let repeated = |name: &'static str, short: char, meta: &'static str, help: &'static str| {
            Arg::new(name)
                .short(short)
                .long(name)
                .value_name(meta)
                .help(help)
                .allow_hyphen_values(true)
                .action(ArgAction::Append)
        };

        Command::new("cost-model")
            .args_override_self(true)
            .arg(
                Arg::new("k")
                    .help("2^K bound on the number of rows.")
                    .required(true)
                    .value_parser(value_parser!(usize)),
            )
            .arg(
                repeated(
                    "advice",
                    'a',
                    "R[,R..]",
                    "An advice column with the given rotations. May be repeated.",
                )
                .value_parser(value_parser!(Poly)),
            )
            .arg(
                repeated(
                    "instance",
                    'i',
                    "R[,R..]",
                    "An instance column with the given rotations. May be repeated.",
                )
                .value_parser(value_parser!(Poly)),
            )
            .arg(
                repeated(
                    "fixed",
                    'f',
                    "R[,R..]",
                    "A fixed column with the given rotations. May be repeated.",
                )
                .value_parser(value_parser!(Poly)),
            )
            .arg(
                Arg::new("gate-degree")
                    .short('g')
                    .long("gate-degree")
                    .value_name("D")
                    .help("Maximum degree of the custom gates.")
                    .allow_hyphen_values(true)
                    .default_value("0")
                    .value_parser(value_parser!(usize)),
            )
            .arg(
                repeated(
                    "lookup",
                    'l',
                    "N,I,T",
                    "A lookup over N columns with max input degree I and max table degree T. May be repeated.",
                )
                .value_parser(value_parser!(Lookup)),
            )
            .arg(
                repeated(
                    "permutation",
                    'p',
                    "N",
                    "A permutation over N columns. May be repeated.",
                )
                .value_parser(value_parser!(Permutation)),
            )
    }

    fn try_parse_from<I, T>(args: I) -> Result<Self, clap::Error>
    where
        I: IntoIterator<Item = T>,
        T: Into<OsString> + Clone,
    {
        let mut matches = Self::command().try_get_matches_from(args)?;
        fn all<T: Clone + Send + Sync + 'static>(matches: &mut ArgMatches, id: &str) -> Vec<T> {
            matches
                .remove_many(id)
                .map(Iterator::collect)
                .unwrap_or_default()
        }
        Ok(CostOptions {
            advice: all(&mut matches, "advice"),
            instance: all(&mut matches, "instance"),
            fixed: all(&mut matches, "fixed"),
            gate_degree: matches.remove_one("gate-degree").expect("has a default"),
            lookup: all(&mut matches, "lookup"),
            permutation: all(&mut matches, "permutation"),
            k: matches.remove_one("k").expect("is required"),
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Poly {
    rotations: Vec<isize>,
}

impl FromStr for Poly {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut rotations: Vec<isize> =
            s.split(',').map(|r| r.parse()).collect::<Result<_, _>>()?;
        rotations.sort_unstable();
        Ok(Poly { rotations })
    }
}

#[derive(Clone, Debug)]
struct Lookup {
    _columns: usize,
    input_deg: usize,
    table_deg: usize,
}

impl FromStr for Lookup {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut parts = s.split(',');
        let _columns = parts.next().unwrap().parse()?;
        let input_deg = parts.next().unwrap().parse()?;
        let table_deg = parts.next().unwrap().parse()?;
        Ok(Lookup {
            _columns,
            input_deg,
            table_deg,
        })
    }
}

impl Lookup {
    fn required_degree(&self) -> usize {
        2 + cmp::max(1, self.input_deg) + cmp::max(1, self.table_deg)
    }

    fn queries(&self) -> impl Iterator<Item = Poly> + use<> {
        // - product commitments at x and x_inv
        // - input commitments at x and x_inv
        // - table commitments at x
        let product = "0,-1".parse().unwrap();
        let input = "0,-1".parse().unwrap();
        let table = "0".parse().unwrap();

        iter::empty()
            .chain(Some(product))
            .chain(Some(input))
            .chain(Some(table))
    }
}

#[derive(Clone, Debug)]
struct Permutation {
    columns: usize,
}

impl FromStr for Permutation {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Permutation {
            columns: s.parse()?,
        })
    }
}

impl Permutation {
    fn required_degree(&self) -> usize {
        cmp::max(self.columns + 1, 2)
    }

    fn queries(&self) -> impl Iterator<Item = Poly> + use<> {
        // - product commitments at x and x_inv
        // - polynomial commitments at x
        let product = "0,-1".parse().unwrap();
        let poly = "0".parse().unwrap();

        iter::empty()
            .chain(Some(product))
            .chain(iter::repeat(poly).take(self.columns))
    }
}

#[derive(Debug)]
struct Circuit {
    /// Power-of-2 bound on the number of rows in the circuit.
    k: usize,
    /// Maximum degree of the circuit.
    max_deg: usize,
    /// Number of advice columns.
    advice_columns: usize,
    /// Number of lookup arguments.
    lookups: usize,
    /// Equality constraint permutation arguments.
    permutations: Vec<Permutation>,
    /// Number of distinct column queries across all gates.
    column_queries: usize,
    /// Number of distinct sets of points in the multiopening argument.
    point_sets: usize,

    estimator: Estimator,
}

impl From<CostOptions> for Circuit {
    fn from(opts: CostOptions) -> Self {
        let max_deg = [1, opts.gate_degree]
            .iter()
            .cloned()
            .chain(opts.lookup.iter().map(|l| l.required_degree()))
            .chain(opts.permutation.iter().map(|p| p.required_degree()))
            .max()
            .unwrap();

        let mut queries: Vec<_> = iter::empty()
            .chain(opts.advice.iter())
            .chain(opts.instance.iter())
            .chain(opts.fixed.iter())
            .cloned()
            .chain(opts.lookup.iter().flat_map(|l| l.queries()))
            .chain(opts.permutation.iter().flat_map(|p| p.queries()))
            .chain(iter::repeat("0".parse().unwrap()).take(max_deg - 1))
            .collect();

        let column_queries = queries.len();
        queries.sort_unstable();
        queries.dedup();
        let point_sets = queries.len();

        Circuit {
            k: opts.k,
            max_deg,
            advice_columns: opts.advice.len(),
            lookups: opts.lookup.len(),
            permutations: opts.permutation,
            column_queries,
            point_sets,
            estimator: Estimator::random(opts.k),
        }
    }
}

impl Circuit {
    fn proof_size(&self) -> usize {
        let size = |points: usize, scalars: usize| points * 32 + scalars * 32;

        // PLONK:
        // - 32 bytes (commitment) per advice column
        // - 3 * 32 bytes (commitments) + 5 * 32 bytes (evals) per lookup argument
        // - 32 bytes (commitment) + 2 * 32 bytes (evals) per permutation argument
        // - 32 bytes (eval) per column per permutation argument
        let plonk = size(1, 0) * self.advice_columns
            + size(3, 5) * self.lookups
            + self
                .permutations
                .iter()
                .map(|p| size(1, 2 + p.columns))
                .sum::<usize>();

        // Vanishing argument:
        // - (max_deg - 1) * 32 bytes (commitments) + (max_deg - 1) * 32 bytes (h_evals)
        //   for quotient polynomial
        // - 32 bytes (eval) per column query
        let vanishing = size(self.max_deg - 1, self.max_deg - 1) + size(0, self.column_queries);

        // Multiopening argument:
        // - f_commitment (32 bytes)
        // - 32 bytes (evals) per set of points in multiopen argument
        let multiopen = size(1, self.point_sets);

        // Polycommit:
        // - s_poly commitment (32 bytes)
        // - inner product argument (k rounds * 2 * 32 bytes)
        // - a (32 bytes)
        // - xi (32 bytes)
        let polycomm = size(1 + 2 * self.k, 2);

        plonk + vanishing + multiopen + polycomm
    }

    fn verification_time(&self) -> Duration {
        // TODO: Estimate cost of BLAKE2b.

        // TODO: This isn't accurate; most of these will have zero scalars.
        let g_scalars = 1 << self.k;

        // - f_commitment
        // - q_commitments
        let multiopen = 1 + self.column_queries;

        // - \iota
        // - Rounds
        // - H
        // - U
        let polycomm = 1 + (2 * self.k) + 1 + 1;

        self.estimator.multiexp(g_scalars + multiopen + polycomm)
    }
}

fn main() {
    let opts = CostOptions::try_parse_from(std::env::args_os()).unwrap_or_else(|e| e.exit());
    let c = Circuit::from(opts);
    println!("{:#?}", c);
    println!("Proof size: {} bytes", c.proof_size());
    println!(
        "Verification: at least {}ms",
        c.verification_time().as_micros() as f64 / 1_000f64
    );
}

#[cfg(test)]
mod tests {
    use clap::error::ErrorKind;

    use super::{CostOptions, Poly};

    fn parse(args: &str) -> Result<CostOptions, clap::Error> {
        CostOptions::try_parse_from(iter_args(args))
    }

    fn iter_args(args: &str) -> impl Iterator<Item = &str> {
        std::iter::once("cost-model").chain(args.split_whitespace())
    }

    fn rotations(polys: &[Poly]) -> Vec<Vec<isize>> {
        polys.iter().map(|p| p.rotations.clone()).collect()
    }

    #[test]
    fn short_options_with_negative_rotations() {
        let opts = parse("-a 0,1 -a 0 -a 0,-1,1 -f 0 -g 4 11").unwrap();
        assert_eq!(opts.k, 11);
        assert_eq!(
            rotations(&opts.advice),
            [vec![0, 1], vec![0], vec![-1, 0, 1]]
        );
        assert_eq!(rotations(&opts.fixed), [vec![0]]);
        assert!(opts.instance.is_empty());
        assert_eq!(opts.gate_degree, 4);
    }

    #[test]
    fn long_options_with_every_column_and_argument_kind() {
        let opts = parse(
            "--advice 0,1 --advice=-1 --instance 0 --fixed=0 --gate-degree=3 \
             --lookup 2,1,3 --lookup 1,1,1 --permutation 3 --permutation=5 12",
        )
        .unwrap();
        assert_eq!(opts.k, 12);
        assert_eq!(rotations(&opts.advice), [vec![0, 1], vec![-1]]);
        assert_eq!(rotations(&opts.instance), [vec![0]]);
        assert_eq!(rotations(&opts.fixed), [vec![0]]);
        assert_eq!(opts.gate_degree, 3);
        let lookups: Vec<_> = opts
            .lookup
            .iter()
            .map(|l| (l._columns, l.input_deg, l.table_deg))
            .collect();
        assert_eq!(lookups, [(2, 1, 3), (1, 1, 1)]);
        let permutations: Vec<_> = opts.permutation.iter().map(|p| p.columns).collect();
        assert_eq!(permutations, [3, 5]);
    }

    #[test]
    fn negative_first_rotation_is_a_value_not_a_flag() {
        let opts = parse("-a -1,0 -i -2 --fixed -1 7").unwrap();
        assert_eq!(rotations(&opts.advice), [vec![-1, 0]]);
        assert_eq!(rotations(&opts.instance), [vec![-2]]);
        assert_eq!(rotations(&opts.fixed), [vec![-1]]);
    }

    #[test]
    fn attached_short_values_and_positional_anywhere() {
        let opts = parse("11 -a0,1 -g4").unwrap();
        assert_eq!(opts.k, 11);
        assert_eq!(rotations(&opts.advice), [vec![0, 1]]);
        assert_eq!(opts.gate_degree, 4);

        let opts = parse("-g 4 -- 9").unwrap();
        assert_eq!(opts.k, 9);
    }

    #[test]
    fn only_k_uses_empty_columns_and_zero_gate_degree() {
        let opts = parse("11").unwrap();
        assert_eq!(opts.k, 11);
        assert_eq!(opts.gate_degree, 0);
        assert!(opts.advice.is_empty());
        assert!(opts.instance.is_empty());
        assert!(opts.fixed.is_empty());
        assert!(opts.lookup.is_empty());
        assert!(opts.permutation.is_empty());
    }

    #[test]
    fn repeated_gate_degree_keeps_the_last_value() {
        assert_eq!(parse("-g 2 --gate-degree 5 11").unwrap().gate_degree, 5);
    }

    #[test]
    fn help_is_reported_with_or_without_k() {
        for args in ["--help", "-h", "--help 11", "11 -h"] {
            let err = parse(args).unwrap_err();
            assert_eq!(err.kind(), ErrorKind::DisplayHelp, "{args}");
            assert_eq!(err.exit_code(), 0, "{args}");
            let help = err.to_string();
            for flag in [
                "--advice",
                "--instance",
                "--fixed",
                "--gate-degree",
                "--lookup",
                "--permutation",
            ] {
                assert!(help.contains(flag), "{args}: help lists {flag}");
            }
        }
    }

    #[test]
    fn invalid_invocations_are_usage_errors() {
        for (args, kind) in [
            ("", ErrorKind::MissingRequiredArgument),
            // The option consumes `11` as its value, so `k` is missing.
            ("--advice 11", ErrorKind::MissingRequiredArgument),
            ("11 12", ErrorKind::UnknownArgument),
            ("-1", ErrorKind::UnknownArgument),
            ("--bogus 11", ErrorKind::UnknownArgument),
            ("-z 11", ErrorKind::UnknownArgument),
            ("abc", ErrorKind::ValueValidation),
            ("--gate-degree x 11", ErrorKind::ValueValidation),
            ("--advice 0,x 11", ErrorKind::ValueValidation),
            ("--permutation -1 11", ErrorKind::ValueValidation),
        ] {
            let err = parse(args).unwrap_err();
            assert_eq!(err.kind(), kind, "{args:?}");
            assert_eq!(err.exit_code(), 2, "{args:?}");
        }
    }
}
