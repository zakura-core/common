import Common

namespace UdonVerify
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024

/-- Pasta's small offset from R/4 gives the sharper loose-product bound. -/
theorem loose_product_bound (p c a b m u : Int)
    (hp : 4*p = (R : Int) + 4*c)
    (hc : 0 < c) (hsmall : 16*c^2 < (R : Int))
    (ha0 : 0 ≤ a) (ha : a < 2*p)
    (hb0 : 0 ≤ b) (hb : b < 2*p)
    (hm0 : 0 ≤ m) (hm : m < (R : Int))
    (hu : u * (R : Int) = a*b + m*p) : u < 2*p := by
  have hR : (R : Int) = 4 * (2^254 : Int) := by norm_num [R, B]
  have hp0 : 0 < p := by norm_num only [R, B] at *; nlinarith only [hp, hc]
  by_contra hbad
  have hu0 : 2*p ≤ u := by omega
  have hab : p*(R : Int) + p ≤ a*b := by
    have h1 := mul_nonneg (show 0 ≤ u-2*p by omega) (show (0 : Int) ≤ R by norm_num [R, B])
    have h2 := mul_nonneg (show 0 ≤ (R : Int)-1-m by omega) (le_of_lt hp0)
    norm_num only [R, B] at *; nlinarith only [hu, h1, h2]
  let A := 2*p-a
  let D := 2*p-b
  let S := A+D
  have hA : 0 < A := by dsimp [A]; omega
  have hD : 0 < D := by dsimp [D]; omega
  have hS : 0 < S := by dsimp [S]; omega
  have hsum : a+b = 4*p-S := by dsimp [S, A, D]; ring
  have hSbound : S ≤ 2*c := by
    by_contra hnot
    have hs : 2*c+1 ≤ S := by omega
    have hsumub : a+b ≤ (R : Int)+2*c-1 := by omega
    have hsq := mul_nonneg (show 0 ≤ (R : Int)+2*c-1-(a+b) by omega)
      (show 0 ≤ (R : Int)+2*c-1+(a+b) by norm_num [R, B]; omega)
    have hdiff := sq_nonneg (a-b)
    have hpp := congrArg (fun x : Int => x*(R : Int)) hp
    norm_num only [R, B] at *; nlinarith only [hsq, hdiff, hpp, hab, hsmall, hc]
  have hAD0 : 0 < A*D := mul_pos hA hD
  have hADsmall : A*D ≤ c^2 := by
    have h1 := sq_nonneg (A-D)
    have h2 := mul_nonneg (show 0 ≤ 2*c-S by omega) (show 0 ≤ 2*c+S by omega)
    dsimp [S] at *
    norm_num only [R, B] at *; nlinarith only [h1, h2]
  have hADp : A*D < p := by norm_num only [R, B] at *; nlinarith only [hADsmall, hsmall, hp, hc]
  let L := 4*c-2*S
  have hL : 0 ≤ L := by dsimp [L]; omega
  have hprod : a*b = p*(R : Int) + p*L + A*D := by
    have hpp := congrArg (fun x : Int => p*x) hp
    dsimp [L, S, A, D]
    norm_num only [R, B] at *; nlinarith only [hpp]
  let k := u-2*p
  let j := L+m-(R : Int)
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hkj : k*(R : Int) = A*D+j*p := by
    dsimp [k, j]
    norm_num only [R, B] at *; nlinarith only [hu, hprod]
  have hj : 0 ≤ j := by
    by_contra hneg
    have h1 := mul_nonneg hk (show (0 : Int) ≤ R by norm_num [R, B])
    have h2 := mul_nonneg (show 0 ≤ -1-j by omega) (le_of_lt hp0)
    norm_num only [R, B] at *; nlinarith only [hkj, hADp, h1, h2]
  have hjub : j ≤ L-1 := by dsimp [j]; omega
  have hADlt : A*D < 2*S*c := by
    have h1 : 0 ≤ 2*c-A := by dsimp [S] at hSbound; omega
    have h2 := mul_nonneg h1 (le_of_lt hD)
    have h3 := mul_pos hc hA
    dsimp [S]
    norm_num only [R, B] at *; nlinarith only [h2, h3]
  have hpos : 0 < A*D+j*c := by norm_num only [R, B] at *; nlinarith only [hAD0, mul_nonneg hj (le_of_lt hc)]
  have hupper : A*D+j*c < (2^254 : Int) := by
    have h1 := mul_nonneg (show 0 ≤ L-1-j by omega) (le_of_lt hc)
    dsimp [L] at h1
    norm_num only [R, B] at *; nlinarith only [h1, hADlt, hsmall, hc]
  have hmultiple : A*D+j*c = (4*k-j)*(2^254 : Int) := by
    have hpp := congrArg (fun x : Int => j*x) hp
    norm_num only [R, B] at *; nlinarith only [hpp, hkj, hR]
  have hcoef : 1 ≤ 4*k-j := by
    by_contra hn
    have h1 : 0 ≤ -(4*k-j) := by omega
    norm_num only [R, B] at *; nlinarith only [hmultiple, hpos, mul_nonneg h1 (show (0 : Int) ≤ 2^254 by norm_num)]
  norm_num only [R, B] at *; nlinarith only [hmultiple, hupper, mul_nonneg (show 0 ≤ 4*k-j-1 by omega)
    (show (0 : Int) ≤ 2^254 by norm_num)]

end UdonVerify
