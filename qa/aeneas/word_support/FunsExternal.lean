module
public import Aeneas
public import Word.Types
@[expose] public section

open Aeneas Std Result

/-- The pinned Rust standard-library body: two overflowing additions and the disjoint flag OR. -/
@[rust_fun "core::num::{u64}::carrying_add"]
def core.num.U64.carrying_add (lhs rhs : U64) (carry : Bool) : Result (U64 × Bool) := do
  let (first, carry1) ← lift (Aeneas.Std.core.num.U64.overflowing_add lhs rhs)
  let input ← lift (UScalar.cast_fromBool .U64 carry)
  let (second, carry2) ← lift (Aeneas.Std.core.num.U64.overflowing_add first input)
  ok (second, carry1 || carry2)

/-- The pinned Rust standard-library body: two overflowing subtractions and the disjoint flag OR. -/
@[rust_fun "core::num::{u64}::borrowing_sub"]
def core.num.U64.borrowing_sub (lhs rhs : U64) (borrow : Bool) : Result (U64 × Bool) := do
  let (first, borrow1) ← lift (Aeneas.Std.core.num.U64.overflowing_sub lhs rhs)
  let input ← lift (UScalar.cast_fromBool .U64 borrow)
  let (second, borrow2) ← lift (Aeneas.Std.core.num.U64.overflowing_sub first input)
  ok (second, borrow1 || borrow2)
