import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace UdonVerify.SafeGcd
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

structure Vertex where
  x : Int
  y : Int
  deriving DecidableEq, Inhabited, Repr

abbrev Point := ℚ × ℚ
abbrev Vertices := _root_.Array Vertex

def point (v : Vertex) : Point := (v.x, v.y)

def mix (a b c : ℚ) (p q r : Point) : Point :=
  (a * p.1 + b * q.1 + c * r.1, a * p.2 + b * q.2 + c * r.2)

/-- Explicit convex combinations of the listed integer vertices. -/
inductive Hull (vertices : Vertices) : Point → Prop
  | vertex {v : Vertex} (h : v ∈ vertices) : Hull vertices (point v)
  | mix (a b c : ℚ) {p q r : Point} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
      (hsum : a + b + c = 1) (hp : Hull vertices p) (hq : Hull vertices q)
      (hr : Hull vertices r) : Hull vertices (SafeGcd.mix a b c p q r)

def orientation (a b p : Vertex) : Int :=
  (b.x - a.x) * (p.y - a.y) - (b.y - a.y) * (p.x - a.x)

theorem orientation_swap (a b p : Vertex) : orientation b a p = -orientation a b p := by
  unfold orientation
  ring

theorem triangle_mem (vertices : Vertices) (a b c p : Vertex)
    (ha : a ∈ vertices) (hb : b ∈ vertices) (hc : c ∈ vertices)
    (harea : 0 < orientation a b c)
    (h0 : 0 ≤ orientation b c p) (h1 : 0 ≤ orientation c a p) (h2 : 0 ≤ orientation a b p) :
    Hull vertices (point p) := by
  let d : ℚ := orientation a b c
  let w0 : ℚ := (orientation b c p : ℚ) / d
  let w1 : ℚ := (orientation c a p : ℚ) / d
  let w2 : ℚ := (orientation a b p : ℚ) / d
  have hd : 0 < d := by dsimp [d]; exact_mod_cast harea
  have hdNonzero : d ≠ 0 := ne_of_gt hd
  have hw0 : 0 ≤ w0 := div_nonneg (by exact_mod_cast h0) hd.le
  have hw1 : 0 ≤ w1 := div_nonneg (by exact_mod_cast h1) hd.le
  have hw2 : 0 ≤ w2 := div_nonneg (by exact_mod_cast h2) hd.le
  have hsum : w0 + w1 + w2 = 1 := by
    dsimp [w0, w1, w2]
    field_simp
    dsimp [d, orientation]
    push_cast
    ring
  have hmix : mix w0 w1 w2 (point a) (point b) (point c) = point p := by
    apply Prod.ext <;> dsimp [mix, point, w0, w1, w2]
    · field_simp
      dsimp [d, orientation]
      push_cast
      ring
    · field_simp
      dsimp [d, orientation]
      push_cast
      ring
  rw [← hmix]
  exact Hull.mix w0 w1 w2 hw0 hw1 hw2 hsum (Hull.vertex ha) (Hull.vertex hb) (Hull.vertex hc)

theorem segment_x_mem (vertices : Vertices) (a b p : Vertex)
    (ha : a ∈ vertices) (hb : b ∈ vertices) (horder : a.x < b.x)
    (hleft : a.x ≤ p.x) (hright : p.x ≤ b.x) (hline : orientation a b p = 0) :
    Hull vertices (point p) := by
  let d : ℚ := (b.x : ℚ) - a.x
  let t : ℚ := ((p.x : ℚ) - a.x) / d
  have hd : 0 < d := by dsimp [d]; exact_mod_cast sub_pos.mpr horder
  have ht : 0 ≤ t := div_nonneg (by exact_mod_cast sub_nonneg.mpr hleft) hd.le
  have htBound : t ≤ 1 := by
    apply (div_le_one₀ hd).mpr
    dsimp [d]
    exact_mod_cast sub_le_sub_right hright a.x
  have hlineRat : ((b.x : ℚ) - a.x) * ((p.y : ℚ) - a.y) -
      ((b.y : ℚ) - a.y) * ((p.x : ℚ) - a.x) = 0 := by
    exact_mod_cast hline
  have hmix : mix (1 - t) t 0 (point a) (point b) (point a) = point p := by
    apply Prod.ext <;> dsimp [mix, point, t]
    · field_simp
      dsimp [d]
      ring
    · field_simp
      dsimp [d]
      nlinarith only [hlineRat]
  rw [← hmix]
  exact Hull.mix (1 - t) t 0 (sub_nonneg.mpr htBound) ht (by rfl)
    (by ring) (Hull.vertex ha) (Hull.vertex hb) (Hull.vertex ha)

theorem segment_y_mem (vertices : Vertices) (a b p : Vertex)
    (ha : a ∈ vertices) (hb : b ∈ vertices) (horder : a.y < b.y)
    (hleft : a.y ≤ p.y) (hright : p.y ≤ b.y) (hline : orientation a b p = 0) :
    Hull vertices (point p) := by
  let d : ℚ := (b.y : ℚ) - a.y
  let t : ℚ := ((p.y : ℚ) - a.y) / d
  have hd : 0 < d := by dsimp [d]; exact_mod_cast sub_pos.mpr horder
  have ht : 0 ≤ t := div_nonneg (by exact_mod_cast sub_nonneg.mpr hleft) hd.le
  have htBound : t ≤ 1 := by
    apply (div_le_one₀ hd).mpr
    dsimp [d]
    exact_mod_cast sub_le_sub_right hright a.y
  have hlineRat : ((b.x : ℚ) - a.x) * ((p.y : ℚ) - a.y) -
      ((b.y : ℚ) - a.y) * ((p.x : ℚ) - a.x) = 0 := by
    exact_mod_cast hline
  have hmix : mix (1 - t) t 0 (point a) (point b) (point a) = point p := by
    apply Prod.ext <;> dsimp [mix, point, t]
    · field_simp
      dsimp [d]
      nlinarith only [hlineRat]
    · field_simp
      dsimp [d]
      ring
  rw [← hmix]
  exact Hull.mix (1 - t) t 0 (sub_nonneg.mpr htBound) ht (by rfl)
    (by ring) (Hull.vertex ha) (Hull.vertex hb) (Hull.vertex ha)

inductive Branch where
  | swap
  | add
  | even
  deriving DecidableEq, Repr

def transform (branch : Branch) (v : Vertex) : Vertex :=
  match branch with
  | .swap => ⟨2 * v.y, v.y - v.x⟩
  | .add => ⟨2 * v.x, v.y + v.x⟩
  | .even => ⟨2 * v.x, v.y⟩

def transformPoint (branch : Branch) (p : Point) : Point :=
  match branch with
  | .swap => (2 * p.2, p.2 - p.1)
  | .add => (2 * p.1, p.2 + p.1)
  | .even => (2 * p.1, p.2)

theorem transform_point (branch : Branch) (v : Vertex) :
    transformPoint branch (point v) = point (transform branch v) := by
  cases branch <;> simp [transformPoint, point, transform]

theorem transform_mix (branch : Branch) (a b c : ℚ) (p q r : Point) :
    transformPoint branch (mix a b c p q r) =
      mix a b c (transformPoint branch p) (transformPoint branch q) (transformPoint branch r) := by
  cases branch <;> apply Prod.ext <;> simp only [transformPoint, mix] <;> ring

theorem hull_transform (branch : Branch) (source target : Vertices)
    (hvertices : ∀ v ∈ source, Hull target (point (transform branch v)))
    (p : Point) (hp : Hull source p) : Hull target (transformPoint branch p) := by
  induction hp with
  | vertex h => simpa only [transform_point] using hvertices _ h
  | mix a b c ha hb hc hsum _ _ _ ihp ihq ihr =>
      rw [transform_mix]
      exact Hull.mix a b c ha hb hc hsum ihp ihq ihr

#print axioms triangle_mem
#print axioms segment_x_mem
#print axioms segment_y_mem
#print axioms hull_transform

end UdonVerify.SafeGcd
