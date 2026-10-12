import CommonSigned62Math
open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

theorem unpack62_join (a b : Nat) (k : Fin 4) (ha : a < 2^(62-2*k.val)) :
    a ||| ((b * 2^(62-2*k.val)) % 2^64) =
      a + 2^(62-2*k.val) * (b % 2^(2+2*k.val)) := by
  have hhigh : (b * 2^(62-2*k.val)) % 2^64 =
      2^(62-2*k.val) * (b % 2^(2+2*k.val)) := by
    fin_cases k <;> norm_num at * <;> omega
  rw [hhigh,Nat.or_comm,←Nat.two_pow_add_eq_or_of_lt ha]
  omega

def unpacked62Digit (v : Signed62) : Nat → Nat
  | 0 => v[0]!.val.toNat + 2^62*(v[1]!.val.toNat % 4)
  | 1 => v[1]!.val.toNat/4 + 2^60*(v[2]!.val.toNat % 16)
  | 2 => v[2]!.val.toNat/16 + 2^58*(v[3]!.val.toNat % 64)
  | 3 => v[3]!.val.toNat/64 + 2^56*v[4]!.val.toNat
  | _ => 0

theorem unpacked62_value (v : Signed62) (hn : signed62Normalized v)
    (htop : 0≤v[4]!.val ∧ v[4]!.val<128) :
    (unpacked62Digit v 0 + 2^64*unpacked62Digit v 1 +
      (2^64)^2*unpacked62Digit v 2 + (2^64)^3*unpacked62Digit v 3 : Nat) =
      signed62Value v := by
  have h0 := (hn ⟨0,by decide⟩).1
  have h1 := (hn ⟨1,by decide⟩).1
  have h2 := (hn ⟨2,by decide⟩).1
  have h3 := (hn ⟨3,by decide⟩).1
  change 0≤v[0]!.val at h0
  change 0≤v[1]!.val at h1
  change 0≤v[2]!.val at h2
  change 0≤v[3]!.val at h3
  have d1 := Nat.mod_add_div v[1]!.val.toNat 4
  have d2 := Nat.mod_add_div v[2]!.val.toNat 16
  have d3 := Nat.mod_add_div v[3]!.val.toNat 64
  have hd1 := congrArg (fun n:Nat=>(n:Int)) d1
  have hd2 := congrArg (fun n:Nat=>(n:Int)) d2
  have hd3 := congrArg (fun n:Nat=>(n:Int)) d3
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Int.toNat_of_nonneg h1,Int.toNat_of_nonneg h2,Int.toNat_of_nonneg h3] at hd1 hd2 hd3
  simp only [unpacked62Digit,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,
    Int.toNat_of_nonneg h0,Int.toNat_of_nonneg h1,Int.toNat_of_nonneg h2,
    Int.toNat_of_nonneg h3,Int.toNat_of_nonneg htop.1,signed62Value,signedRadix]
  norm_num only at hd1 hd2 hd3 ⊢
  omega

#print axioms unpack62_join
#print axioms unpacked62_value
end UdonVerify.CommonSigned62
