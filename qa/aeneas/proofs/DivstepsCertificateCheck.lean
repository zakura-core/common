import DivstepsPointCheck
import DivstepsStrip

namespace UdonVerify.SafeGcd
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

structure Node where
  delta : Int
  scaleX : Int
  scaleY : Int
  compact : Vertices
  terminal : Bool
  deriving Inhabited, Repr

abbrev Nodes := _root_.Array Node

def Node.vertices (node : Node) : Vertices :=
  ⟨node.compact.toList.map fun v => ⟨node.scaleX * v.x, node.scaleY * v.y⟩⟩

def nodeIndexAux (nodes : Nodes) (delta : Int) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
      if hi ≤ lo then lo else
        let mid := (lo + hi) / 2
        if nodes[mid]!.delta < delta
        then nodeIndexAux nodes delta fuel (mid + 1) hi
        else nodeIndexAux nodes delta fuel lo mid

def nodeIndex (nodes : Nodes) (delta : Int) : Nat :=
  nodeIndexAux nodes delta nodes.size 0 nodes.size

def nextDelta (delta : Int) (branch : Branch) : Int :=
  match branch with
  | .swap => 1 - delta
  | .add | .even => delta + 1

def branchCheck (target : Nodes) (node : Node) (branch : Branch) : Bool :=
  let index := nodeIndex target (nextDelta node.delta branch)
  if index < target.size then
    let destination := target[index]!
    decide (destination.delta = nextDelta node.delta branch) &&
      node.vertices.toList.all (fun v => pointCheck destination.vertices (transform branch v))
  else false

def terminalCheck (modulusBound scale : Int) (node : Node) : Bool :=
  if node.terminal then
    node.vertices.toList.all (fun v => decide (-scale < v.y * modulusBound ∧ v.y * modulusBound < scale))
  else true

def stepCheck (modulusBound scale : Int) (source target : Nodes) : Bool :=
  target.toList.all (terminalCheck modulusBound scale) &&
    source.toList.all (fun node => if node.terminal then true else
      branchCheck target node .even && branchCheck target node (if 0 < node.delta then .swap else .add))

def finalCheck (nodes : Nodes) : Bool := nodes.toList.all (fun node => node.terminal)

theorem node_mem (nodes : Nodes) (index : Nat) (h : index < nodes.size) : nodes[index]! ∈ nodes := by
  rw [getElem!_pos nodes index h]
  exact _root_.Array.mem_of_getElem rfl

theorem branch_check_sound (target : Nodes) (node : Node) (branch : Branch)
    (hcheck : branchCheck target node branch = true) :
    ∃ destination ∈ target, destination.delta = nextDelta node.delta branch ∧
      ∀ p, Hull node.vertices p → Hull destination.vertices (transformPoint branch p) := by
  unfold branchCheck at hcheck
  dsimp only at hcheck
  by_cases hindex : nodeIndex target (nextDelta node.delta branch) < target.size
  · simp only [hindex, ↓reduceIte] at hcheck
    have h := Bool.and_eq_true_iff.mp hcheck
    refine ⟨_, node_mem target _ hindex, of_decide_eq_true h.1, ?_⟩
    intro p hp
    apply hull_transform branch node.vertices _ ?_ p hp
    intro v hv
    have hvertices := List.all_eq_true.mp h.2
    exact point_check_sound _ _ (hvertices v (_root_.Array.mem_toList_iff.mpr hv))
  · simp only [hindex, ↓reduceIte, Bool.false_eq_true] at hcheck

theorem terminal_check_sound (modulusBound scale : Int) (node : Node)
    (hmodulus : 0 < modulusBound) (hterminal : node.terminal = true)
    (hcheck : terminalCheck modulusBound scale node = true)
    (p : Point) (hp : Hull node.vertices p) :
    -((scale : ℚ) / modulusBound) < p.2 ∧ p.2 < (scale : ℚ) / modulusBound := by
  unfold terminalCheck at hcheck
  simp only [hterminal, ↓reduceIte] at hcheck
  have hvertices := List.all_eq_true.mp hcheck
  apply hull_strip node.vertices _ ?_ p hp
  intro v hv
  have h := of_decide_eq_true (hvertices v (_root_.Array.mem_toList_iff.mpr hv))
  have hmodulusRat : 0 < (modulusBound : ℚ) := by exact_mod_cast hmodulus
  constructor
  · rw [← neg_div]
    apply (div_lt_iff₀ hmodulusRat).mpr
    exact_mod_cast h.1
  · apply (lt_div_iff₀ hmodulusRat).mpr
    exact_mod_cast h.2

theorem integer_zero_of_strip (modulus modulusBound scale g : Int)
    (hmodulus : 0 < modulus) (hscale : 0 < scale) (hbound : modulus ≤ modulusBound)
    (hstrip : -((scale : ℚ) / modulusBound) < (g : ℚ) * scale / modulus ∧
      (g : ℚ) * scale / modulus < (scale : ℚ) / modulusBound) : g = 0 := by
  have hmodulusRat : 0 < (modulus : ℚ) := by exact_mod_cast hmodulus
  have hscaleRat : 0 < (scale : ℚ) := by exact_mod_cast hscale
  have hboundRat : (modulus : ℚ) ≤ modulusBound := by exact_mod_cast hbound
  have hratio : 0 < (scale : ℚ) / modulus := div_pos hscaleRat hmodulusRat
  have hratioBound : (scale : ℚ) / modulusBound ≤ (scale : ℚ) / modulus :=
    div_le_div_of_nonneg_left hscaleRat.le hmodulusRat hboundRat
  rw [mul_div_assoc] at hstrip
  by_cases hnegative : g < 0
  · have hle : (g : ℚ) ≤ -1 := by exact_mod_cast (show g ≤ -1 by omega)
    have hmul := mul_le_mul_of_nonneg_right hle hratio.le
    nlinarith only [hstrip.1, hratioBound, hmul]
  · by_cases hpositive : 0 < g
    · have hle : 1 ≤ (g : ℚ) := by exact_mod_cast (show 1 ≤ g by omega)
      have hmul := mul_le_mul_of_nonneg_right hle hratio.le
      nlinarith only [hstrip.2, hratioBound, hmul]
    · omega

theorem terminal_integer_zero (modulus modulusBound scale : Int) (node : Node)
    (hmodulus : 0 < modulus) (hscale : 0 < scale) (hbound : modulus ≤ modulusBound)
    (hterminal : node.terminal = true)
    (hcheck : terminalCheck modulusBound scale node = true) (f g : Int)
    (hhull : Hull node.vertices ((f : ℚ) * scale / modulus, (g : ℚ) * scale / modulus)) :
    g = 0 := by
  exact integer_zero_of_strip modulus modulusBound scale g hmodulus hscale hbound
    (terminal_check_sound modulusBound scale node (by omega) hterminal hcheck _ hhull)

theorem step_check_sound (modulusBound scale : Int) (source target : Nodes)
    (hcheck : stepCheck modulusBound scale source target = true) :
    (∀ node ∈ target, terminalCheck modulusBound scale node = true) ∧
    (∀ node ∈ source, node.terminal = false →
      branchCheck target node .even = true ∧
      branchCheck target node (if 0 < node.delta then .swap else .add) = true) := by
  have h := Bool.and_eq_true_iff.mp hcheck
  refine ⟨?_, ?_⟩
  · simpa only [_root_.Array.mem_toList_iff] using List.all_eq_true.mp h.1
  intro node hnode hterminal
  have hnodeCheck := List.all_eq_true.mp h.2 node (_root_.Array.mem_toList_iff.mpr hnode)
  simp only [hterminal] at hnodeCheck
  exact Bool.and_eq_true_iff.mp hnodeCheck

theorem final_check_sound (nodes : Nodes) (hcheck : finalCheck nodes = true) :
    ∀ node ∈ nodes, node.terminal = true := by
  simpa only [_root_.Array.mem_toList_iff] using List.all_eq_true.mp hcheck

#print axioms branch_check_sound
#print axioms terminal_check_sound
#print axioms integer_zero_of_strip
#print axioms terminal_integer_zero
#print axioms step_check_sound
#print axioms final_check_sound

end UdonVerify.SafeGcd
