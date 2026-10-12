import DivstepsCertificateCheck

namespace UdonVerify.SafeGcd
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

structure BranchWitness where
  destination : Nat
  triangles : List Nat
  deriving Repr

def pointsWitnessCheck (target : Vertices) (branch : Branch) : List Vertex → List Nat → Bool
  | [], [] => true
  | vertex :: vertices, k :: indices =>
      pointCandidateCheck target (transform branch vertex) k &&
        pointsWitnessCheck target branch vertices indices
  | _, _ => false

def branchWitnessCheck (target : Nodes) (source : Node) (branch : Branch)
    (witness : BranchWitness) : Bool :=
  if witness.destination < target.size then
    let destination := target[witness.destination]!
    decide (destination.delta = nextDelta source.delta branch) &&
      pointsWitnessCheck destination.vertices branch source.vertices.toList witness.triangles
  else false

def nodeWitnessCheck (target : Nodes) (node : Node) (witness : BranchWitness × BranchWitness) : Bool :=
  if node.terminal then true else
    branchWitnessCheck target node .even witness.1 &&
    branchWitnessCheck target node (if 0 < node.delta then .swap else .add) witness.2

def sourceWitnessCheck (target : Nodes) : List Node → List (BranchWitness × BranchWitness) → Bool
  | [], [] => true
  | node :: nodes, witness :: witnesses =>
      nodeWitnessCheck target node witness && sourceWitnessCheck target nodes witnesses
  | _, _ => false

def stepWitnessCheck (modulusBound scale : Int) (source target : Nodes)
    (witnesses : List (BranchWitness × BranchWitness)) : Bool :=
  target.toList.all (terminalCheck modulusBound scale) &&
    sourceWitnessCheck target source.toList witnesses

def BranchValid (target : Nodes) (node : Node) (branch : Branch) : Prop :=
  ∃ destination ∈ target, destination.delta = nextDelta node.delta branch ∧
    ∀ p, Hull node.vertices p → Hull destination.vertices (transformPoint branch p)

def StepValid (modulusBound scale : Int) (source target : Nodes) : Prop :=
  (∀ node ∈ target, terminalCheck modulusBound scale node = true) ∧
  (∀ node ∈ source, node.terminal = false →
    BranchValid target node .even ∧ BranchValid target node (if 0 < node.delta then .swap else .add))

theorem points_witness_check_sound (target : Vertices) (branch : Branch)
    (vertices : List Vertex) (indices : List Nat)
    (hcheck : pointsWitnessCheck target branch vertices indices = true) :
    ∀ v ∈ vertices, Hull target (point (transform branch v)) := by
  induction vertices generalizing indices with
  | nil => simp
  | cons v vertices ih =>
      cases indices with
      | nil => simp [pointsWitnessCheck] at hcheck
      | cons k indices =>
          have h := Bool.and_eq_true_iff.mp hcheck
          intro query hquery
          rcases List.mem_cons.mp hquery with hquery | hquery
          · subst query
            exact point_candidate_check_sound _ _ k h.1
          · exact ih indices h.2 query hquery

theorem branch_witness_check_sound (target : Nodes) (source : Node) (branch : Branch)
    (witness : BranchWitness) (hcheck : branchWitnessCheck target source branch witness = true) :
    BranchValid target source branch := by
  unfold branchWitnessCheck at hcheck
  by_cases hindex : witness.destination < target.size
  · simp only [hindex, ↓reduceIte] at hcheck
    have h := Bool.and_eq_true_iff.mp hcheck
    refine ⟨_, node_mem target witness.destination hindex, of_decide_eq_true h.1, ?_⟩
    apply hull_transform branch source.vertices _ ?_
    intro v hv
    exact points_witness_check_sound _ branch source.vertices.toList witness.triangles h.2 v
      (_root_.Array.mem_toList_iff.mpr hv)
  · simp only [hindex, ↓reduceIte, Bool.false_eq_true] at hcheck

theorem source_witness_check_sound (target : Nodes) (source : List Node)
    (witnesses : List (BranchWitness × BranchWitness))
    (hcheck : sourceWitnessCheck target source witnesses = true) :
    ∀ node ∈ source, node.terminal = false →
      BranchValid target node .even ∧ BranchValid target node (if 0 < node.delta then .swap else .add) := by
  induction source generalizing witnesses with
  | nil => simp
  | cons node nodes ih =>
      cases witnesses with
      | nil => simp [sourceWitnessCheck] at hcheck
      | cons witness witnesses =>
          have h := Bool.and_eq_true_iff.mp hcheck
          intro query hquery hnonterminal
          rcases List.mem_cons.mp hquery with hquery | hquery
          · subst query
            simp only [nodeWitnessCheck, hnonterminal, Bool.false_eq_true, ↓reduceIte] at h
            have hbranches := Bool.and_eq_true_iff.mp h.1
            exact ⟨branch_witness_check_sound _ _ _ _ hbranches.1,
              branch_witness_check_sound _ _ _ _ hbranches.2⟩
          · exact ih witnesses h.2 query hquery hnonterminal

theorem step_witness_check_sound (modulusBound scale : Int) (source target : Nodes)
    (witnesses : List (BranchWitness × BranchWitness))
    (hcheck : stepWitnessCheck modulusBound scale source target witnesses = true) :
    StepValid modulusBound scale source target := by
  have h := Bool.and_eq_true_iff.mp hcheck
  constructor
  · simpa only [_root_.Array.mem_toList_iff] using List.all_eq_true.mp h.1
  · simpa only [_root_.Array.mem_toList_iff] using source_witness_check_sound target source.toList witnesses h.2

theorem step_check_valid (modulusBound scale : Int) (source target : Nodes)
    (hcheck : stepCheck modulusBound scale source target = true) :
    StepValid modulusBound scale source target := by
  have h := step_check_sound modulusBound scale source target hcheck
  refine ⟨h.1, ?_⟩
  intro node hnode hterminal
  have hbranches := h.2 node hnode hterminal
  exact ⟨branch_check_sound target node _ hbranches.1,
    branch_check_sound target node _ hbranches.2⟩

theorem source_witness_check_nil (target : Nodes) : sourceWitnessCheck target [] [] = true := rfl

theorem source_witness_check_cons (target : Nodes) (node : Node) (nodes : List Node)
    (witness : BranchWitness × BranchWitness) (witnesses : List (BranchWitness × BranchWitness))
    (hhead : nodeWitnessCheck target node witness = true)
    (htail : sourceWitnessCheck target nodes witnesses = true) :
    sourceWitnessCheck target (node :: nodes) (witness :: witnesses) = true :=
  Bool.and_eq_true_iff.mpr ⟨hhead, htail⟩

theorem step_witness_check_intro (modulusBound scale : Int) (source target : Nodes)
    (witnesses : List (BranchWitness × BranchWitness))
    (hterminal : target.toList.all (terminalCheck modulusBound scale) = true)
    (hsource : sourceWitnessCheck target source.toList witnesses = true) :
    stepWitnessCheck modulusBound scale source target witnesses = true :=
  Bool.and_eq_true_iff.mpr ⟨hterminal, hsource⟩

#print axioms points_witness_check_sound
#print axioms branch_witness_check_sound
#print axioms source_witness_check_sound
#print axioms step_witness_check_sound
#print axioms step_check_valid
#print axioms source_witness_check_cons
#print axioms step_witness_check_intro

end UdonVerify.SafeGcd
