//! Buffer serialization of circuit keys. Derived prover caches are not encoded.

use super::{Circuit, ConstraintSystem, ProvingKey, VerifyingKey, keygen, permutation};
use crate::{
    arithmetic::CurveAffine,
    poly::{EvaluationDomain, LagrangeCoeff, Polynomial},
};
use ff::{FromUniformBytes, PrimeField, WithSmallOrderMulGroup};
use std::io::{self, Read};

impl<C: CurveAffine> VerifyingKey<C> {
    /// Writes this verifying key to a buffer using checked, portable encodings.
    ///
    /// The format contains the one-byte domain exponent, a little-endian `u32`
    /// fixed-commitment count, compressed fixed and permutation commitments, then
    /// selector activations packed eight rows per byte (least-significant bit first).
    /// There is no version field. The circuit configuration is not serialized.
    pub fn write<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        let k = u8::try_from(self.domain.k()).map_err(|_| {
            io::Error::new(io::ErrorKind::InvalidInput, "domain exponent exceeds u8")
        })?;
        let count = u32::try_from(self.fixed_commitments.len()).map_err(|_| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                "fixed-commitment count exceeds u32",
            )
        })?;
        writer.write_all(&[k])?;
        writer.write_all(&count.to_le_bytes())?;
        for commitment in &self.fixed_commitments {
            writer.write_all(commitment.to_bytes().as_ref())?;
        }
        self.permutation.write(writer)?;
        for selector in &self.selectors {
            writer.write_all(selector)?;
        }
        Ok(())
    }
}

impl<C: CurveAffine> VerifyingKey<C>
where
    C::Scalar: FromUniformBytes<64>,
{
    /// Reads a verifying key written by [`Self::write`], without circuit synthesis
    /// or commitment parameters. `ConcreteCircuit` must configure the same circuit
    /// that was used to generate the key, including its selector allocation order.
    ///
    /// Encodings and dimensions are checked, but this does not authenticate the key
    /// or establish that it belongs to the intended circuit. Only load keys from a
    /// trusted source. Callers loading large keys should bound the domain exponent
    /// as well as the input length: derived state can be much larger than the encoding.
    /// Exactly one key is consumed; trailing bytes are left in the reader.
    pub fn read<R: io::Read, ConcreteCircuit: Circuit<C::Scalar>>(
        reader: &mut R,
    ) -> io::Result<Self> {
        Self::read_parts::<R, ConcreteCircuit>(reader).map(|(vk, _, _)| vk)
    }

    #[allow(clippy::type_complexity)]
    fn read_parts<R: io::Read, ConcreteCircuit: Circuit<C::Scalar>>(
        reader: &mut R,
    ) -> io::Result<(Self, Vec<(usize, usize, usize)>, ConcreteCircuit::Config)> {
        let invalid = |message| io::Error::new(io::ErrorKind::InvalidData, message);
        let mut k = [0];
        reader.read_exact(&mut k)?;
        let k = u32::from(k[0]);
        if k > C::Scalar::S || k >= usize::BITS || k >= u64::BITS {
            return Err(invalid("unsupported circuit size"));
        }

        let mut cs = ConstraintSystem::default();
        let config = ConcreteCircuit::configure(&mut cs);
        let degree =
            u32::try_from(cs.degree()).map_err(|_| invalid("unsupported circuit degree"))?;
        // The quotient needs ceil(log2(degree - 1)) additional domain bits.
        let extended_k = k + (u32::BITS - (degree - 2).leading_zeros());
        if extended_k > C::Scalar::S
            || extended_k >= usize::BITS
            || extended_k >= u64::BITS
            || (1usize << extended_k) > isize::MAX as usize / size_of::<C::Scalar>()
        {
            return Err(invalid("unsupported extended domain size"));
        }
        let n = 1usize << k;
        if n < cs.minimum_rows() {
            return Err(invalid("not enough rows for circuit"));
        }

        let mut count = [0; 4];
        reader.read_exact(&mut count)?;
        let count = u32::from_le_bytes(count) as usize;
        if count < cs.num_fixed_columns || count - cs.num_fixed_columns > cs.num_selectors {
            return Err(invalid("unexpected fixed-commitment count"));
        }
        let fixed_commitments = (0..count)
            .map(|_| {
                let mut repr = C::Repr::default();
                reader.read_exact(repr.as_mut())?;
                Option::from(C::from_bytes(&repr))
                    .ok_or_else(|| invalid("invalid fixed commitment"))
            })
            .collect::<io::Result<Vec<_>>>()?;
        let permutation = permutation::VerifyingKey::read(reader, &cs.permutation)?;
        let mut selectors = Vec::new();
        for _ in 0..cs.num_selectors {
            let mut selector = Vec::new();
            // minimum_rows() is at least eight, so n is divisible by eight.
            (&mut *reader)
                .take((n / 8) as u64)
                .read_to_end(&mut selector)?;
            if selector.len() != n / 8 {
                return Err(io::ErrorKind::UnexpectedEof.into());
            }
            selectors.push(selector);
        }
        let activations = selectors
            .iter()
            .map(|selector| {
                (0..n)
                    .map(|row| (selector[row / 8] >> (row % 8)) & 1 == 1)
                    .collect()
            })
            .collect();
        let (cs, _, compressed_selectors) = cs.compress_selectors(activations);
        if count != cs.num_fixed_columns {
            return Err(invalid("fixed-commitment count does not match selectors"));
        }
        let domain = EvaluationDomain::new(degree, k);
        Ok((
            Self::from_parts(domain, fixed_commitments, permutation, cs, selectors),
            compressed_selectors,
            config,
        ))
    }
}

impl<C: CurveAffine> ProvingKey<C> {
    /// Writes this proving key to a buffer.
    ///
    /// The format is the embedded [`VerifyingKey::write`] encoding followed by
    /// fixed and permutation polynomials in Lagrange form, in column order. Each
    /// polynomial has a little-endian `u32` length followed by canonical field
    /// representations (endianness as specified by [`PrimeField`]). Derived
    /// polynomials and caches are rebuilt on read, not serialized.
    pub fn write<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        self.vk.write(writer)?;
        for polynomial in &self.fixed_values {
            write_polynomial(writer, polynomial)?;
        }
        self.permutation.write(writer)
    }
}

impl<C: CurveAffine> ProvingKey<C>
where
    C::Scalar: FromUniformBytes<64>,
{
    /// Reads a proving key written by [`Self::write`]. The circuit and trust
    /// requirements of [`VerifyingKey::read`] apply here as well. Polynomial
    /// lengths and field encodings are checked, but their consistency with the
    /// embedded verifying key is not authenticated.
    ///
    /// Does not synthesize the circuit or require commitment parameters. Rebuilds
    /// derived polynomials and prover caches, including opted-in circuit
    /// configurations. Opaque floor plans and parameter-dependent prepared
    /// commitments use the prover's normal fallback paths instead.
    pub fn read<R: io::Read, ConcreteCircuit: Circuit<C::Scalar>>(
        reader: &mut R,
    ) -> io::Result<Self> {
        let (vk, compressed_selectors, config) =
            VerifyingKey::read_parts::<R, ConcreteCircuit>(reader)?;
        let circuit_config = if ConcreteCircuit::CACHE_CONFIGURATION {
            ConcreteCircuit::cache_configuration(&config)
        } else {
            None
        };
        let fixed = (0..vk.cs.num_fixed_columns)
            .map(|_| read_polynomial(reader, &vk.domain))
            .collect::<io::Result<Vec<_>>>()?;
        let (permutation, fft_twiddles) = permutation::ProvingKey::read(reader, &vk)?;
        Ok(keygen::build_pk(
            vk,
            fixed,
            permutation,
            fft_twiddles,
            compressed_selectors,
            None,
            circuit_config,
        ))
    }
}

pub(super) fn write_polynomial<W: io::Write, F: PrimeField>(
    writer: &mut W,
    values: &[F],
) -> io::Result<()> {
    let len = u32::try_from(values.len()).map_err(|_| {
        io::Error::new(io::ErrorKind::InvalidInput, "polynomial length exceeds u32")
    })?;
    writer.write_all(&len.to_le_bytes())?;
    for value in values {
        writer.write_all(value.to_repr().as_ref())?;
    }
    Ok(())
}

pub(super) fn read_polynomial<R: io::Read, F: WithSmallOrderMulGroup<3>>(
    reader: &mut R,
    domain: &EvaluationDomain<F>,
) -> io::Result<Polynomial<F, LagrangeCoeff>> {
    let mut len = [0; 4];
    reader.read_exact(&mut len)?;
    let len = u32::from_le_bytes(len) as usize;
    if len != 1usize << domain.k() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "unexpected polynomial length",
        ));
    }
    // Grow only as values are read, rather than allocating from an untrusted length.
    let mut values = Vec::new();
    for _ in 0..len {
        let mut repr = F::Repr::default();
        reader.read_exact(repr.as_mut())?;
        values.push(Option::<F>::from(F::from_repr(repr)).ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidData, "invalid field encoding in key")
        })?);
    }
    Ok(domain.lagrange_from_vec(values))
}
