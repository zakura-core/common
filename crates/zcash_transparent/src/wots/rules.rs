//! The consensus rules for spending from accounts and creating control outputs.

use alloc::{collections::BTreeMap, vec::Vec};
use core::fmt;

use super::{ControlOutput, FormError, VERSION, WotsInput, classify};

/// What a transaction that passed [`check_accounts`] spends from accounts.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct AccountCheck {
    /// Indices of the inputs these rules fully validated. The script interpreter must not
    /// run on them.
    pub wots_inputs: Vec<usize>,
    /// Number of verified authorizations, one per account spent from.
    pub authorizations: u32,
}

/// Why a transaction breaks the account rules.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AccountError {
    /// An account input's script signature is not an allowed form.
    Form {
        /// The input's index.
        input: usize,
        /// What is wrong with it.
        error: FormError,
    },
    /// An account script, or a spent or created control output, has an unknown version.
    Version,
    /// An account is spent from without exactly one authorization: one control input, or on
    /// the first spend, one deposit input carrying a signature.
    Authorizations,
    /// The authorization's spare index is outside the key set.
    Spare,
    /// The authorization does not sign this transaction under the expected root.
    Signature,
    /// No signature digest is available for the authorizing input.
    Digest,
    /// The step cannot advance past `u32::MAX`.
    StepOverflow,
    /// The transaction does not create exactly one control output for an account it spends
    /// from, at the next step.
    Successor,
    /// The transaction creates a control output for an account it does not spend from.
    UnauthorizedControlOutput,
}

impl fmt::Display for AccountError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Form { input, error } => {
                write!(f, "input {input} is not an allowed account form: {error:?}")
            }
            Self::Version => f.write_str("unknown account version"),
            Self::Authorizations => f.write_str("an account needs exactly one authorization"),
            Self::Spare => f.write_str("spare index outside the key set"),
            Self::Signature => f.write_str("authorization does not sign this transaction"),
            Self::Digest => f.write_str("no signature digest for the authorizing input"),
            Self::StepOverflow => f.write_str("account step cannot advance"),
            Self::Successor => {
                f.write_str("expected exactly one control output for the account at the next step")
            }
            Self::UnauthorizedControlOutput => {
                f.write_str("control output created without the account's authorization")
            }
        }
    }
}

/// For one account: each authorizing input, its expected root and the step it advances from.
type Authorizations = Vec<(usize, super::Authorization, [u8; 32], u32)>;

/// Checks the account rules for one transaction.
///
/// - `inputs` holds each input's script signature and the script of the output it spends.
/// - `outputs` holds each output's script.
/// - `digest(index)` returns the ZIP 244 `SIGHASH_ALL` signature digest for an input, or
///   `None` if the transaction has no such digest.
///
/// For every account the transaction spends from, exactly one input must authorize it,
/// and the transaction must create exactly one control output for it at the next step.
/// No control output may be created for any other account, so a coinbase transaction can
/// create none.
pub fn check_accounts(
    inputs: &[(&[u8], &[u8])],
    outputs: &[&[u8]],
    mut digest: impl FnMut(usize) -> Option<[u8; 32]>,
) -> Result<AccountCheck, AccountError> {
    let mut check = AccountCheck::default();
    let mut accounts: BTreeMap<[u8; 20], Authorizations> = BTreeMap::new();
    for (index, (script_sig, spent_script)) in inputs.iter().enumerate() {
        let Some(form) = classify(script_sig, spent_script) else {
            continue;
        };
        let form = form.map_err(|error| AccountError::Form {
            input: index,
            error,
        })?;
        check.wots_inputs.push(index);
        let authorizations = accounts.entry(form.account_hash()).or_default();
        match form {
            WotsInput::Control {
                control,
                authorization,
            } => {
                if control.version != VERSION {
                    return Err(AccountError::Version);
                }
                authorizations.push((index, authorization, control.root, control.step));
            }
            WotsInput::SigningDeposit {
                account,
                authorization,
            } => {
                if account.version != VERSION {
                    return Err(AccountError::Version);
                }
                authorizations.push((index, authorization, account.root, 0));
            }
            WotsInput::CoveredDeposit { account } => {
                if account.version != VERSION {
                    return Err(AccountError::Version);
                }
            }
        }
    }

    let mut created: BTreeMap<[u8; 20], Vec<ControlOutput>> = BTreeMap::new();
    for script in outputs {
        if let Some(control) = ControlOutput::parse(script) {
            if control.version != VERSION {
                return Err(AccountError::Version);
            }
            created.entry(control.account).or_default().push(control);
        }
    }
    if created
        .keys()
        .any(|account| !accounts.contains_key(account))
    {
        return Err(AccountError::UnauthorizedControlOutput);
    }

    for (account, authorizations) in accounts {
        let [(index, authorization, root, step)] = authorizations.as_slice() else {
            return Err(AccountError::Authorizations);
        };
        let next = step.checked_add(1).ok_or(AccountError::StepOverflow)?;
        let digest = digest(*index).ok_or(AccountError::Digest)?;
        let recovered = authorization
            .recover_root(digest)
            .ok_or(AccountError::Spare)?;
        if &recovered != root {
            return Err(AccountError::Signature);
        }
        match created.get(&account).map(Vec::as_slice) {
            Some([successor]) if successor.step == next => {}
            _ => return Err(AccountError::Successor),
        }
        check.authorizations += 1;
    }
    Ok(check)
}
