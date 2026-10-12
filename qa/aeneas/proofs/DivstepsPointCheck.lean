import DivstepsGeometry

namespace UdonVerify.SafeGcd
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

def fanIndexAux (vertices : Vertices) (p : Vertex) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then lo else
      let mid := (lo + hi) / 2
      if 0 ≤ orientation vertices[0]! vertices[mid]! p
      then fanIndexAux vertices p fuel mid hi
      else fanIndexAux vertices p fuel lo mid

def fanIndex (vertices : Vertices) (p : Vertex) : Nat :=
  fanIndexAux vertices p vertices.size 1 (vertices.size - 1)

def segmentCheck (a b p : Vertex) : Bool :=
  if a.x < b.x then decide (a.x ≤ p.x ∧ p.x ≤ b.x ∧ orientation a b p = 0)
  else if b.x < a.x then decide (b.x ≤ p.x ∧ p.x ≤ a.x ∧ orientation b a p = 0)
  else if a.y < b.y then decide (a.y ≤ p.y ∧ p.y ≤ b.y ∧ orientation a b p = 0)
  else if b.y < a.y then decide (b.y ≤ p.y ∧ p.y ≤ a.y ∧ orientation b a p = 0)
  else decide (p = a)

def pointCheck (vertices : Vertices) (p : Vertex) : Bool :=
  if vertices.size = 0 then false
  else if vertices.size = 1 then decide (p = vertices[0]!)
  else if vertices.size = 2 then segmentCheck vertices[0]! vertices[1]! p
  else
    let k := fanIndex vertices p
    let a := vertices[0]!
    let b := vertices[k]!
    let c := vertices[k + 1]!
    decide (k + 1 < vertices.size ∧ 0 < orientation a b c ∧
      0 ≤ orientation b c p ∧ 0 ≤ orientation c a p ∧ 0 ≤ orientation a b p)

def pointCandidateCheck (vertices : Vertices) (p : Vertex) (k : Nat) : Bool :=
  if vertices.size = 0 then false
  else if vertices.size = 1 then decide (p = vertices[0]!)
  else if vertices.size = 2 then segmentCheck vertices[0]! vertices[1]! p
  else
    let a := vertices[0]!
    let b := vertices[k]!
    let c := vertices[k + 1]!
    decide (k + 1 < vertices.size ∧ 0 < orientation a b c ∧
      0 ≤ orientation b c p ∧ 0 ≤ orientation c a p ∧ 0 ≤ orientation a b p)

theorem vertex_mem (vertices : Vertices) (i : Nat) (h : i < vertices.size) :
    vertices[i]! ∈ vertices := by
  rw [getElem!_pos vertices i h]
  exact _root_.Array.mem_of_getElem rfl

theorem segment_check_sound (vertices : Vertices) (a b p : Vertex)
    (ha : a ∈ vertices) (hb : b ∈ vertices) (hcheck : segmentCheck a b p = true) :
    Hull vertices (point p) := by
  unfold segmentCheck at hcheck
  split_ifs at hcheck with hx hxr hy hyr
  · have h := of_decide_eq_true hcheck
    exact segment_x_mem vertices a b p ha hb hx h.1 h.2.1 h.2.2
  · have h := of_decide_eq_true hcheck
    exact segment_x_mem vertices b a p hb ha hxr h.1 h.2.1 h.2.2
  · have h := of_decide_eq_true hcheck
    exact segment_y_mem vertices a b p ha hb hy h.1 h.2.1 h.2.2
  · have h := of_decide_eq_true hcheck
    exact segment_y_mem vertices b a p hb ha hyr h.1 h.2.1 h.2.2
  · have hp : p = a := of_decide_eq_true hcheck
    subst p
    exact Hull.vertex ha

/-- Search only selects a candidate; checked indices and orientations certify containment. -/
theorem point_check_sound (vertices : Vertices) (p : Vertex) (hcheck : pointCheck vertices p = true) :
    Hull vertices (point p) := by
  unfold pointCheck at hcheck
  split_ifs at hcheck with hzero hone htwo
  · have hp : p = vertices[0]! := of_decide_eq_true hcheck
    rw [hp]
    exact Hull.vertex (vertex_mem vertices 0 (by omega))
  · exact segment_check_sound vertices vertices[0]! vertices[1]! p
      (vertex_mem vertices 0 (by omega)) (vertex_mem vertices 1 (by omega)) hcheck
  · let k := fanIndex vertices p
    have hcondition : k + 1 < vertices.size ∧ 0 < orientation vertices[0]! vertices[k]! vertices[k + 1]! ∧
        0 ≤ orientation vertices[k]! vertices[k + 1]! p ∧
        0 ≤ orientation vertices[k + 1]! vertices[0]! p ∧ 0 ≤ orientation vertices[0]! vertices[k]! p :=
      of_decide_eq_true hcheck
    exact triangle_mem vertices vertices[0]! vertices[k]! vertices[k + 1]! p
      (vertex_mem vertices 0 (by omega)) (vertex_mem vertices k (by omega))
      (vertex_mem vertices (k + 1) hcondition.1) hcondition.2.1 hcondition.2.2.1
      hcondition.2.2.2.1 hcondition.2.2.2.2

theorem point_candidate_check_sound (vertices : Vertices) (p : Vertex) (k : Nat)
    (hcheck : pointCandidateCheck vertices p k = true) : Hull vertices (point p) := by
  unfold pointCandidateCheck at hcheck
  split_ifs at hcheck with hzero hone htwo
  · have hp : p = vertices[0]! := of_decide_eq_true hcheck
    rw [hp]
    exact Hull.vertex (vertex_mem vertices 0 (by omega))
  · exact segment_check_sound vertices vertices[0]! vertices[1]! p
      (vertex_mem vertices 0 (by omega)) (vertex_mem vertices 1 (by omega)) hcheck
  · have hcondition : k + 1 < vertices.size ∧ 0 < orientation vertices[0]! vertices[k]! vertices[k + 1]! ∧
        0 ≤ orientation vertices[k]! vertices[k + 1]! p ∧
        0 ≤ orientation vertices[k + 1]! vertices[0]! p ∧ 0 ≤ orientation vertices[0]! vertices[k]! p :=
      of_decide_eq_true hcheck
    exact triangle_mem vertices vertices[0]! vertices[k]! vertices[k + 1]! p
      (vertex_mem vertices 0 (by omega)) (vertex_mem vertices k (by omega))
      (vertex_mem vertices (k + 1) hcondition.1) hcondition.2.1 hcondition.2.2.1
      hcondition.2.2.2.1 hcondition.2.2.2.2

#print axioms point_check_sound
#print axioms point_candidate_check_sound

end UdonVerify.SafeGcd
