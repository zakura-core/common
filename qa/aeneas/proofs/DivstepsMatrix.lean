import DivstepsBounds

namespace UdonVerify.SafeGcd
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

structure Matrix where
  u : Int
  v : Int
  q : Int
  r : Int
  deriving DecidableEq, Repr

def identityMatrix : Matrix := ⟨1, 0, 0, 1⟩

def matrixStep (branch : Branch) (matrix : Matrix) : Matrix :=
  match branch with
  | .swap => ⟨2 * matrix.q, 2 * matrix.r, matrix.q - matrix.u, matrix.r - matrix.v⟩
  | .add => ⟨2 * matrix.u, 2 * matrix.v, matrix.q + matrix.u, matrix.r + matrix.v⟩
  | .even => ⟨2 * matrix.u, 2 * matrix.v, matrix.q, matrix.r⟩

def matrixAction (matrix : Matrix) (f g : Int) : Vertex :=
  ⟨matrix.u * f + matrix.v * g, matrix.q * f + matrix.r * g⟩

def scaleVertex (scale : Int) (vertex : Vertex) : Vertex :=
  ⟨scale * vertex.x, scale * vertex.y⟩

def transitionMatrix : Nat → State → Matrix
  | 0, _ => identityMatrix
  | n + 1, state =>
      let current := iterate n state
      matrixStep (chooseBranch current.delta current.g) (transitionMatrix n state)

theorem matrix_step_rows (branch : Branch) (matrix : Matrix) (bound : Int) (hbound : 0 ≤ bound)
    (hfirst : |matrix.u| + |matrix.v| ≤ bound) (hsecond : |matrix.q| + |matrix.r| ≤ bound) :
    |(matrixStep branch matrix).u| + |(matrixStep branch matrix).v| ≤ 2 * bound ∧
      |(matrixStep branch matrix).q| + |(matrixStep branch matrix).r| ≤ 2 * bound := by
  cases branch with
  | swap =>
      change |2 * matrix.q| + |2 * matrix.r| ≤ 2 * bound ∧
        |matrix.q - matrix.u| + |matrix.r - matrix.v| ≤ 2 * bound
      constructor
      · norm_num only [abs_mul]
        linarith only [hsecond]
      · linarith only [hfirst, hsecond, abs_sub matrix.q matrix.u, abs_sub matrix.r matrix.v]
  | add =>
      change |2 * matrix.u| + |2 * matrix.v| ≤ 2 * bound ∧
        |matrix.q + matrix.u| + |matrix.r + matrix.v| ≤ 2 * bound
      constructor
      · norm_num only [abs_mul]
        linarith only [hfirst]
      · linarith only [hfirst, hsecond, abs_add_le matrix.q matrix.u, abs_add_le matrix.r matrix.v]
  | even =>
      change |2 * matrix.u| + |2 * matrix.v| ≤ 2 * bound ∧
        |matrix.q| + |matrix.r| ≤ 2 * bound
      constructor
      · norm_num only [abs_mul]
        linarith only [hfirst]
      · linarith only [hsecond, hbound]

theorem matrix_step_action (branch : Branch) (matrix : Matrix) (f g : Int) :
    matrixAction (matrixStep branch matrix) f g = transform branch (matrixAction matrix f g) := by
  cases branch <;> dsimp [matrixAction, matrixStep, transform] <;> congr 1 <;> ring

theorem transform_scale (branch : Branch) (scale : Int) (vertex : Vertex) :
    transform branch (scaleVertex scale vertex) = scaleVertex scale (transform branch vertex) := by
  cases branch <;> dsimp [transform, scaleVertex] <;> congr 1 <;> ring

theorem transition_matrix_rows (n : Nat) (state : State) :
    |(transitionMatrix n state).u| + |(transitionMatrix n state).v| ≤ 2 ^ n ∧
      |(transitionMatrix n state).q| + |(transitionMatrix n state).r| ≤ 2 ^ n := by
  induction n with
  | zero => norm_num [transitionMatrix, identityMatrix]
  | succ n ih =>
      have h := matrix_step_rows (chooseBranch (iterate n state).delta (iterate n state).g)
        (transitionMatrix n state) (2 ^ n) (by positivity) ih.1 ih.2
      simpa only [transitionMatrix, pow_succ, mul_comm] using h

theorem transition_matrix_action (n : Nat) (state : State) (hodd : state.f % 2 = 1) :
    matrixAction (transitionMatrix n state) state.f state.g =
      scaleVertex (2 ^ n) ⟨(iterate n state).f, (iterate n state).g⟩ := by
  induction n with
  | zero => simp [transitionMatrix, identityMatrix, matrixAction, scaleVertex, iterate]
  | succ n ih =>
      rw [transitionMatrix, matrix_step_action, ih, transform_scale,
        integer_step_doubled _ (iterate_odd n state hodd)]
      dsimp only [scaleVertex, iterate]
      rw [pow_succ]
      congr 1 <;> ring

theorem transition_matrix_62 (state : State) (hodd : state.f % 2 = 1) :
    (transitionMatrix 62 state).u * state.f + (transitionMatrix 62 state).v * state.g =
        2 ^ 62 * (iterate 62 state).f ∧
      (transitionMatrix 62 state).q * state.f + (transitionMatrix 62 state).r * state.g =
        2 ^ 62 * (iterate 62 state).g := by
  have h := transition_matrix_action 62 state hodd
  exact ⟨congrArg Vertex.x h, congrArg Vertex.y h⟩

#print axioms transition_matrix_rows
#print axioms transition_matrix_action
#print axioms transition_matrix_62

end UdonVerify.SafeGcd
