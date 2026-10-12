import DivstepsInteger
import DivstepsWitnessCheck

namespace UdonVerify.SafeGcd
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

def Covered (modulus modulusBound scale : Int) (nodes : Nodes) (state : State) : Prop :=
  state.g = 0 ∨ ∃ node ∈ nodes, node.delta = state.delta ∧
    terminalCheck modulusBound scale node = true ∧
    Hull node.vertices (scaledPoint modulus scale state)

def initialNode : Node := ⟨1, 1, 1, #[⟨1, 0⟩, ⟨1, 1⟩], false⟩
def initialNodes : Nodes := #[initialNode]

theorem initial_covered (modulus modulusBound x : Int) (hmodulus : 0 < modulus)
    (hx : 0 ≤ x) (hbound : x ≤ modulus) :
    Covered modulus modulusBound 1 initialNodes ⟨1, modulus, x⟩ := by
  right
  refine ⟨initialNode, by simp [initialNodes], rfl, rfl, ?_⟩
  have h := initial_hull modulus x hmodulus hx hbound
  simpa [Node.vertices, initialNode, scaledPoint, ne_of_gt hmodulus] using h

theorem covered_step (modulus modulusBound scale : Int) (source target : Nodes) (state : State)
    (hmodulus : 0 < modulus) (hscale : 0 < scale) (hbound : modulus ≤ modulusBound)
    (hodd : state.f % 2 = 1)
    (hcheck : StepValid modulusBound (2 * scale) source target)
    (hcovered : Covered modulus modulusBound scale source state) :
    Covered modulus modulusBound (2 * scale) target (integerStep state) := by
  rcases hcovered with hzero | ⟨node, hnode, hdelta, hterminalCheck, hhull⟩
  · exact Or.inl (integer_step_zero state hzero)
  by_cases hterminal : node.terminal = true
  · have hzero := terminal_integer_zero modulus modulusBound scale node hmodulus hscale hbound
      hterminal hterminalCheck state.f state.g hhull
    exact Or.inl (integer_step_zero state hzero)
  · have hnonterminal : node.terminal = false := by
      cases hvalue : node.terminal <;> simp_all
    have hchecks := hcheck
    have hbranches := hchecks.2 node hnode hnonterminal
    have hbranch : BranchValid target node (chooseBranch state.delta state.g) := by
      unfold chooseBranch
      split_ifs with heven hpositive
      · exact hbranches.1
      · simpa only [hdelta, hpositive, ↓reduceIte] using hbranches.2
      · simpa only [hdelta, hpositive, ↓reduceIte] using hbranches.2
    rcases hbranch with ⟨destination, hdest, hdestDelta, htransport⟩
    right
    refine ⟨destination, hdest, ?_, hchecks.1 destination hdest, ?_⟩
    · rw [hdestDelta, hdelta, integer_step_delta]
    · rw [integer_step_scaled modulus scale state hodd]
      exact htransport _ hhull

theorem covered_final (modulus modulusBound scale : Int) (nodes : Nodes) (state : State)
    (hmodulus : 0 < modulus) (hscale : 0 < scale) (hbound : modulus ≤ modulusBound)
    (hcheck : finalCheck nodes = true) (hcovered : Covered modulus modulusBound scale nodes state) :
    state.g = 0 := by
  rcases hcovered with hzero | ⟨node, hnode, _, hterminalCheck, hhull⟩
  · exact hzero
  · exact terminal_integer_zero modulus modulusBound scale node hmodulus hscale hbound
      (final_check_sound nodes hcheck node hnode) hterminalCheck state.f state.g hhull

/-- A certificate supplies hulls only. Every transition and terminal strip is checked. -/
theorem certificate_convergence (modulus modulusBound x : Int) (last : Nat) (stages : Nat → Nodes)
    (hmodulus : 0 < modulus) (hbound : modulus ≤ modulusBound) (hodd : modulus % 2 = 1)
    (hx : 0 ≤ x) (hxBound : x ≤ modulus) (hinitial : stages 0 = initialNodes)
    (hsteps : ∀ n < last,
      StepValid modulusBound (2 ^ (n + 1)) (stages n) (stages (n + 1)))
    (hfinal : finalCheck (stages last) = true) :
    (iterate last ⟨1, modulus, x⟩).g = 0 := by
  have hcovered : ∀ n, n ≤ last →
      Covered modulus modulusBound (2 ^ n) (stages n) (iterate n ⟨1, modulus, x⟩) := by
    intro n
    induction n with
    | zero =>
        intro _
        simpa only [hinitial, iterate, pow_zero] using
          initial_covered modulus modulusBound x hmodulus hx hxBound
    | succ n ih =>
        intro hn
        have hnBound : n < last := by omega
        have hpower : (2 : Int) ^ (n + 1) = 2 * 2 ^ n := by ring
        rw [iterate, hpower]
        exact covered_step modulus modulusBound (2 ^ n) _ _ _ hmodulus
          (by positivity) hbound (iterate_odd n _ hodd)
          (by simpa only [hpower] using hsteps n hnBound) (ih (by omega))
  exact covered_final modulus modulusBound (2 ^ last) _ _ hmodulus (by positivity) hbound
    hfinal (hcovered last le_rfl)

#print axioms initial_covered
#print axioms covered_step
#print axioms covered_final
#print axioms certificate_convergence

end UdonVerify.SafeGcd
