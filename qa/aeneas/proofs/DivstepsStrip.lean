import DivstepsGeometry

namespace UdonVerify.SafeGcd
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem mix_upper_bound (a b c x y z bound : ℚ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a + b + c = 1)
    (hx : x < bound) (hy : y < bound) (hz : z < bound) :
    a * x + b * y + c * z < bound := by
  have hsumScaled : a * bound + b * bound + c * bound = bound := by
    calc
      _ = (a + b + c) * bound := by ring
      _ = bound := by rw [hsum, one_mul]
  by_cases haPositive : 0 < a
  · have hax := mul_lt_mul_of_pos_left hx haPositive
    have hby := mul_le_mul_of_nonneg_left hy.le hb
    have hcz := mul_le_mul_of_nonneg_left hz.le hc
    linarith
  · have haZero : a = 0 := by linarith
    by_cases hbPositive : 0 < b
    · have hby := mul_lt_mul_of_pos_left hy hbPositive
      have hcz := mul_le_mul_of_nonneg_left hz.le hc
      simp only [haZero, zero_mul] at *
      linarith
    · have hbZero : b = 0 := by linarith
      have hcOne : c = 1 := by simpa only [haZero, hbZero, zero_add] using hsum
      simpa only [haZero, hbZero, hcOne, zero_mul, one_mul, zero_add] using hz

theorem hull_strip (vertices : Vertices) (bound : ℚ)
    (hvertices : ∀ v ∈ vertices, -bound < (v.y : ℚ) ∧ (v.y : ℚ) < bound)
    (p : Point) (hp : Hull vertices p) : -bound < p.2 ∧ p.2 < bound := by
  induction hp with
  | vertex h => exact hvertices _ h
  | @mix a b c p q r ha hb hc hsum hp hq hr ihp ihq ihr =>
      constructor
      · have h := mix_upper_bound a b c (-p.2) (-q.2) (-r.2) bound ha hb hc hsum
          (by linarith [ihp.1]) (by linarith [ihq.1]) (by linarith [ihr.1])
        dsimp [mix]
        linarith
      · exact mix_upper_bound a b c _ _ _ bound ha hb hc hsum ihp.2 ihq.2 ihr.2

theorem initial_hull (p x : Int) (hp : 0 < p) (hx : 0 ≤ x) (hbound : x ≤ p) :
    Hull #[⟨1, 0⟩, ⟨1, 1⟩] (1, (x : ℚ) / p) := by
  have hpRat : 0 < (p : ℚ) := by exact_mod_cast hp
  let t : ℚ := (x : ℚ) / p
  have ht : 0 ≤ t := div_nonneg (by exact_mod_cast hx) hpRat.le
  have htBound : t ≤ 1 := by
    apply (div_le_one₀ hpRat).mpr
    exact_mod_cast hbound
  have h0 : (⟨1, 0⟩ : Vertex) ∈ #[⟨1, 0⟩, ⟨1, 1⟩] := by simp
  have h1 : (⟨1, 1⟩ : Vertex) ∈ #[⟨1, 0⟩, ⟨1, 1⟩] := by simp
  have h := Hull.mix (1 - t) t 0 (sub_nonneg.mpr htBound) ht (by rfl)
    (by ring) (Hull.vertex h0) (Hull.vertex h1) (Hull.vertex h0)
  simpa only [mix, point, Int.cast_one, Int.cast_zero, mul_one, mul_zero, zero_add, add_zero,
    sub_add_cancel] using h

#print axioms hull_strip
#print axioms initial_hull

end UdonVerify.SafeGcd
