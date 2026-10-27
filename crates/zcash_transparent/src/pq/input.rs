//! Recognizing the three forms of input that spend from an account.

use super::{AccountScript, Authorization, ControlOutput, authorization::PUSHES, pushes};

/// An input spending from an account. The script interpreter must not run on these.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AccountInput {
    /// Spends the account's control output, signed by a spare of its step.
    Control {
        /// The control output being spent.
        control: ControlOutput,
        /// The signature authorizing the whole transaction for this account.
        authorization: Authorization,
    },
    /// Spends a payment to the account and carries the first spend's authorization.
    SigningDeposit {
        /// The account's redeem script.
        account: AccountScript,
        /// The signature by a step-0 spare.
        authorization: Authorization,
    },
    /// Spends a payment to the account, authorized by another input of the transaction.
    CoveredDeposit {
        /// The account's redeem script.
        account: AccountScript,
    },
}

impl AccountInput {
    /// The account hash `A` this input spends from.
    pub fn account_hash(&self) -> [u8; 20] {
        match self {
            Self::Control { control, .. } => control.account,
            Self::SigningDeposit { account, .. } | Self::CoveredDeposit { account } => {
                account.account_hash()
            }
        }
    }
}

/// An account input whose script signature is not one of the allowed forms.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FormError {
    /// A control input's script signature is not exactly one authorization.
    ControlScriptSig,
    /// A deposit input's script signature is neither the redeem script alone nor an
    /// authorization followed by it.
    DepositScriptSig,
}

/// Recognizes an input spending from an account, given its script signature and the
/// script of the output it spends.
///
/// Returns `None` for any other input, which the script interpreter handles. A payment to
/// an account can only be redeemed through its account script, which contains an opcode
/// the interpreter rejects, so returning `None` never lets an account input skip checks.
pub fn classify(script_sig: &[u8], spent_script: &[u8]) -> Option<Result<AccountInput, FormError>> {
    if let Some(control) = ControlOutput::parse(spent_script) {
        let form = pushes(script_sig)
            .filter(|values| values.len() == PUSHES)
            .and_then(|values| Authorization::from_pushes(&values))
            .map(|authorization| AccountInput::Control {
                control,
                authorization,
            })
            .ok_or(FormError::ControlScriptSig);
        return Some(form);
    }

    let script_hash: &[u8; 20] = match spent_script {
        [0xa9, 0x14, hash @ .., 0x87] => hash.try_into().ok()?,
        _ => return None,
    };
    let values = pushes(script_sig)?;
    let (last, rest) = values.split_last()?;
    let account = AccountScript::parse(last)?;
    if &account.account_hash() != script_hash {
        return None;
    }
    let form = match rest.len() {
        0 => Ok(AccountInput::CoveredDeposit { account }),
        PUSHES => Authorization::from_pushes(rest)
            .map(|authorization| AccountInput::SigningDeposit {
                account,
                authorization,
            })
            .ok_or(FormError::DepositScriptSig),
        _ => Err(FormError::DepositScriptSig),
    };
    Some(form)
}
