import Common

open Aeneas Std Result
open zakura_udon.field.pasta.word

namespace UdonVerify
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem multiply_outer_unfold (lhs rhs : A4) (product : A8) (index : Usize) :
    multiply_wide_loop0 lhs rhs product index = (do
      let r ← multiply_wide_loop0.body lhs rhs product index
      match r with
      | .done r => ok r
      | .cont (a, i) => multiply_wide_loop0 lhs rhs a i) := by
  unfold multiply_wide_loop0
  rw [loop]
  congr 1
  funext r
  cases r with
  | done r => rfl
  | cont r => rcases r with ⟨a, i⟩; rfl

theorem multiply_inner_unfold (lhs rhs : A4) (product : A8)
    (i : Usize) (carry : U64) (j : Usize) :
    multiply_wide_loop0_loop0 lhs rhs product i carry j = (do
      let r ← multiply_wide_loop0_loop0.body lhs rhs i product carry j
      match r with
      | .done r => ok r
      | .cont (a, c, j) => multiply_wide_loop0_loop0 lhs rhs a i c j) := by
  unfold multiply_wide_loop0_loop0
  rw [loop]
  congr 1
  funext r
  cases r with
  | done r => rfl
  | cont r => rcases r with ⟨a, c, j⟩; rfl

@[step]
theorem multiply_wide_spec (lhs rhs : A4) :
    multiply_wide lhs rhs ⦃ out => val8 out = val4 lhs * val4 rhs ⦄ := by
  unfold multiply_wide
  rw [multiply_outer_unfold]
  unfold multiply_wide_loop0.body
  simp only [show (0#usize) < 4#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  rw [multiply_inner_unfold]
  unfold multiply_wide_loop0_loop0.body
  simp only [show (0#usize) < 4#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  step +scalarTac -grind with Usize.add_spec as ⟨ix00, hix00⟩
  try
    have hixeq00 : ix00 = 0#usize := by scalar_tac
    subst ix00
  step +scalarTac -grind as ⟨acc00, hacc00⟩
  step +scalarTac -grind as ⟨l00, hl00⟩
  step +scalarTac -grind as ⟨r00, hr00⟩
  step +scalarTac -grind with kernel_mac_identity as ⟨pair00, h00⟩
  rcases pair00 with ⟨lo00, carry00⟩
  try dsimp only
  try simp only [Std.bind_assoc]
  step +scalarTac -grind as ⟨a00, ha00⟩
  step +scalarTac -grind with Usize.add_spec as ⟨j00, hj00⟩
  try
    have hjeq00 : j00 = 1#usize := by scalar_tac
    subst j00
  subst a00
  try simp only [bind_ok]
  rw [multiply_inner_unfold]
  unfold multiply_wide_loop0_loop0.body
  simp only [show (1#usize) < 4#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  step +scalarTac -grind with Usize.add_spec as ⟨ix01, hix01⟩
  try
    have hixeq01 : ix01 = 1#usize := by scalar_tac
    subst ix01
  step +scalarTac -grind as ⟨acc01, hacc01⟩
  step +scalarTac -grind as ⟨l01, hl01⟩
  step +scalarTac -grind as ⟨r01, hr01⟩
  step +scalarTac -grind with kernel_mac_identity as ⟨pair01, h01⟩
  rcases pair01 with ⟨lo01, carry01⟩
  try dsimp only
  try simp only [Std.bind_assoc]
  step +scalarTac -grind as ⟨a01, ha01⟩
  step +scalarTac -grind with Usize.add_spec as ⟨j01, hj01⟩
  try
    have hjeq01 : j01 = 2#usize := by scalar_tac
    subst j01
  subst a01
  try simp only [bind_ok]
  rw [multiply_inner_unfold]
  unfold multiply_wide_loop0_loop0.body
  simp only [show (2#usize) < 4#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  step +scalarTac -grind with Usize.add_spec as ⟨ix02, hix02⟩
  try
    have hixeq02 : ix02 = 2#usize := by scalar_tac
    subst ix02
  step +scalarTac -grind as ⟨acc02, hacc02⟩
  step +scalarTac -grind as ⟨l02, hl02⟩
  step +scalarTac -grind as ⟨r02, hr02⟩
  step +scalarTac -grind with kernel_mac_identity as ⟨pair02, h02⟩
  rcases pair02 with ⟨lo02, carry02⟩
  try dsimp only
  try simp only [Std.bind_assoc]
  step +scalarTac -grind as ⟨a02, ha02⟩
  step +scalarTac -grind with Usize.add_spec as ⟨j02, hj02⟩
  try
    have hjeq02 : j02 = 3#usize := by scalar_tac
    subst j02
  subst a02
  try simp only [bind_ok]
  rw [multiply_inner_unfold]
  unfold multiply_wide_loop0_loop0.body
  simp only [show (3#usize) < 4#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  step +scalarTac -grind with Usize.add_spec as ⟨ix03, hix03⟩
  try
    have hixeq03 : ix03 = 3#usize := by scalar_tac
    subst ix03
  step +scalarTac -grind as ⟨acc03, hacc03⟩
  step +scalarTac -grind as ⟨l03, hl03⟩
  step +scalarTac -grind as ⟨r03, hr03⟩
  step +scalarTac -grind with kernel_mac_identity as ⟨pair03, h03⟩
  rcases pair03 with ⟨lo03, carry03⟩
  try dsimp only
  try simp only [Std.bind_assoc]
  step +scalarTac -grind as ⟨a03, ha03⟩
  step +scalarTac -grind with Usize.add_spec as ⟨j03, hj03⟩
  try
    have hjeq03 : j03 = 4#usize := by scalar_tac
    subst j03
  subst a03
  try simp only [bind_ok]
  rw [multiply_inner_unfold]
  unfold multiply_wide_loop0_loop0.body
  simp only [show ¬ ((4#usize) < 4#usize) from by decide, ite_false, bind_ok]
  try dsimp only
  try simp only [bind_ok, Std.bind_assoc]
  step +scalarTac -grind with Usize.add_spec as ⟨upper0, hupper0⟩
  try
    have hupeq0 : upper0 = 4#usize := by scalar_tac
    subst upper0
  step +scalarTac -grind as ⟨outera0, houtera0⟩
  step +scalarTac -grind with Usize.add_spec as ⟨i0, hi0⟩
  try
    have hieq0 : i0 = 1#usize := by scalar_tac
    subst i0
  subst outera0
  try simp only [bind_ok]
  rw [multiply_outer_unfold]
  unfold multiply_wide_loop0.body
  simp only [show (1#usize) < 4#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  rw [multiply_inner_unfold]
  unfold multiply_wide_loop0_loop0.body
  simp only [show (0#usize) < 4#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  step +scalarTac -grind with Usize.add_spec as ⟨ix10, hix10⟩
  try
    have hixeq10 : ix10 = 1#usize := by scalar_tac
    subst ix10
  step +scalarTac -grind as ⟨acc10, hacc10⟩
  step +scalarTac -grind as ⟨l10, hl10⟩
  step +scalarTac -grind as ⟨r10, hr10⟩
  step +scalarTac -grind with kernel_mac_identity as ⟨pair10, h10⟩
  rcases pair10 with ⟨lo10, carry10⟩
  try dsimp only
  try simp only [Std.bind_assoc]
  step +scalarTac -grind as ⟨a10, ha10⟩
  step +scalarTac -grind with Usize.add_spec as ⟨j10, hj10⟩
  try
    have hjeq10 : j10 = 1#usize := by scalar_tac
    subst j10
  subst a10
  try simp only [bind_ok]
  rw [multiply_inner_unfold]
  unfold multiply_wide_loop0_loop0.body
  simp only [show (1#usize) < 4#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  step +scalarTac -grind with Usize.add_spec as ⟨ix11, hix11⟩
  try
    have hixeq11 : ix11 = 2#usize := by scalar_tac
    subst ix11
  step +scalarTac -grind as ⟨acc11, hacc11⟩
  step +scalarTac -grind as ⟨l11, hl11⟩
  step +scalarTac -grind as ⟨r11, hr11⟩
  step +scalarTac -grind with kernel_mac_identity as ⟨pair11, h11⟩
  rcases pair11 with ⟨lo11, carry11⟩
  try dsimp only
  try simp only [Std.bind_assoc]
  step +scalarTac -grind as ⟨a11, ha11⟩
  step +scalarTac -grind with Usize.add_spec as ⟨j11, hj11⟩
  try
    have hjeq11 : j11 = 2#usize := by scalar_tac
    subst j11
  subst a11
  try simp only [bind_ok]
  rw [multiply_inner_unfold]
  unfold multiply_wide_loop0_loop0.body
  simp only [show (2#usize) < 4#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  step +scalarTac -grind with Usize.add_spec as ⟨ix12, hix12⟩
  try
    have hixeq12 : ix12 = 3#usize := by scalar_tac
    subst ix12
  step +scalarTac -grind as ⟨acc12, hacc12⟩
  step +scalarTac -grind as ⟨l12, hl12⟩
  step +scalarTac -grind as ⟨r12, hr12⟩
  step +scalarTac -grind with kernel_mac_identity as ⟨pair12, h12⟩
  rcases pair12 with ⟨lo12, carry12⟩
  try dsimp only
  try simp only [Std.bind_assoc]
  step +scalarTac -grind as ⟨a12, ha12⟩
  step +scalarTac -grind with Usize.add_spec as ⟨j12, hj12⟩
  try
    have hjeq12 : j12 = 3#usize := by scalar_tac
    subst j12
  subst a12
  try simp only [bind_ok]
  rw [multiply_inner_unfold]
  unfold multiply_wide_loop0_loop0.body
  simp only [show (3#usize) < 4#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  step +scalarTac -grind with Usize.add_spec as ⟨ix13, hix13⟩
  try
    have hixeq13 : ix13 = 4#usize := by scalar_tac
    subst ix13
  step +scalarTac -grind as ⟨acc13, hacc13⟩
  step +scalarTac -grind as ⟨l13, hl13⟩
  step +scalarTac -grind as ⟨r13, hr13⟩
  step +scalarTac -grind with kernel_mac_identity as ⟨pair13, h13⟩
  rcases pair13 with ⟨lo13, carry13⟩
  try dsimp only
  try simp only [Std.bind_assoc]
  step +scalarTac -grind as ⟨a13, ha13⟩
  step +scalarTac -grind with Usize.add_spec as ⟨j13, hj13⟩
  try
    have hjeq13 : j13 = 4#usize := by scalar_tac
    subst j13
  subst a13
  try simp only [bind_ok]
  rw [multiply_inner_unfold]
  unfold multiply_wide_loop0_loop0.body
  simp only [show ¬ ((4#usize) < 4#usize) from by decide, ite_false, bind_ok]
  try dsimp only
  try simp only [bind_ok, Std.bind_assoc]
  step +scalarTac -grind with Usize.add_spec as ⟨upper1, hupper1⟩
  try
    have hupeq1 : upper1 = 5#usize := by scalar_tac
    subst upper1
  step +scalarTac -grind as ⟨outera1, houtera1⟩
  step +scalarTac -grind with Usize.add_spec as ⟨i1, hi1⟩
  try
    have hieq1 : i1 = 2#usize := by scalar_tac
    subst i1
  subst outera1
  try simp only [bind_ok]
  rw [multiply_outer_unfold]
  unfold multiply_wide_loop0.body
  simp only [show (2#usize) < 4#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  rw [multiply_inner_unfold]
  unfold multiply_wide_loop0_loop0.body
  simp only [show (0#usize) < 4#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  step +scalarTac -grind with Usize.add_spec as ⟨ix20, hix20⟩
  try
    have hixeq20 : ix20 = 2#usize := by scalar_tac
    subst ix20
  step +scalarTac -grind as ⟨acc20, hacc20⟩
  step +scalarTac -grind as ⟨l20, hl20⟩
  step +scalarTac -grind as ⟨r20, hr20⟩
  step +scalarTac -grind with kernel_mac_identity as ⟨pair20, h20⟩
  rcases pair20 with ⟨lo20, carry20⟩
  try dsimp only
  try simp only [Std.bind_assoc]
  step +scalarTac -grind as ⟨a20, ha20⟩
  step +scalarTac -grind with Usize.add_spec as ⟨j20, hj20⟩
  try
    have hjeq20 : j20 = 1#usize := by scalar_tac
    subst j20
  subst a20
  try simp only [bind_ok]
  rw [multiply_inner_unfold]
  unfold multiply_wide_loop0_loop0.body
  simp only [show (1#usize) < 4#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  step +scalarTac -grind with Usize.add_spec as ⟨ix21, hix21⟩
  try
    have hixeq21 : ix21 = 3#usize := by scalar_tac
    subst ix21
  step +scalarTac -grind as ⟨acc21, hacc21⟩
  step +scalarTac -grind as ⟨l21, hl21⟩
  step +scalarTac -grind as ⟨r21, hr21⟩
  step +scalarTac -grind with kernel_mac_identity as ⟨pair21, h21⟩
  rcases pair21 with ⟨lo21, carry21⟩
  try dsimp only
  try simp only [Std.bind_assoc]
  step +scalarTac -grind as ⟨a21, ha21⟩
  step +scalarTac -grind with Usize.add_spec as ⟨j21, hj21⟩
  try
    have hjeq21 : j21 = 2#usize := by scalar_tac
    subst j21
  subst a21
  try simp only [bind_ok]
  rw [multiply_inner_unfold]
  unfold multiply_wide_loop0_loop0.body
  simp only [show (2#usize) < 4#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  step +scalarTac -grind with Usize.add_spec as ⟨ix22, hix22⟩
  try
    have hixeq22 : ix22 = 4#usize := by scalar_tac
    subst ix22
  step +scalarTac -grind as ⟨acc22, hacc22⟩
  step +scalarTac -grind as ⟨l22, hl22⟩
  step +scalarTac -grind as ⟨r22, hr22⟩
  step +scalarTac -grind with kernel_mac_identity as ⟨pair22, h22⟩
  rcases pair22 with ⟨lo22, carry22⟩
  try dsimp only
  try simp only [Std.bind_assoc]
  step +scalarTac -grind as ⟨a22, ha22⟩
  step +scalarTac -grind with Usize.add_spec as ⟨j22, hj22⟩
  try
    have hjeq22 : j22 = 3#usize := by scalar_tac
    subst j22
  subst a22
  try simp only [bind_ok]
  rw [multiply_inner_unfold]
  unfold multiply_wide_loop0_loop0.body
  simp only [show (3#usize) < 4#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  step +scalarTac -grind with Usize.add_spec as ⟨ix23, hix23⟩
  try
    have hixeq23 : ix23 = 5#usize := by scalar_tac
    subst ix23
  step +scalarTac -grind as ⟨acc23, hacc23⟩
  step +scalarTac -grind as ⟨l23, hl23⟩
  step +scalarTac -grind as ⟨r23, hr23⟩
  step +scalarTac -grind with kernel_mac_identity as ⟨pair23, h23⟩
  rcases pair23 with ⟨lo23, carry23⟩
  try dsimp only
  try simp only [Std.bind_assoc]
  step +scalarTac -grind as ⟨a23, ha23⟩
  step +scalarTac -grind with Usize.add_spec as ⟨j23, hj23⟩
  try
    have hjeq23 : j23 = 4#usize := by scalar_tac
    subst j23
  subst a23
  try simp only [bind_ok]
  rw [multiply_inner_unfold]
  unfold multiply_wide_loop0_loop0.body
  simp only [show ¬ ((4#usize) < 4#usize) from by decide, ite_false, bind_ok]
  try dsimp only
  try simp only [bind_ok, Std.bind_assoc]
  step +scalarTac -grind with Usize.add_spec as ⟨upper2, hupper2⟩
  try
    have hupeq2 : upper2 = 6#usize := by scalar_tac
    subst upper2
  step +scalarTac -grind as ⟨outera2, houtera2⟩
  step +scalarTac -grind with Usize.add_spec as ⟨i2, hi2⟩
  try
    have hieq2 : i2 = 3#usize := by scalar_tac
    subst i2
  subst outera2
  try simp only [bind_ok]
  rw [multiply_outer_unfold]
  unfold multiply_wide_loop0.body
  simp only [show (3#usize) < 4#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  rw [multiply_inner_unfold]
  unfold multiply_wide_loop0_loop0.body
  simp only [show (0#usize) < 4#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  step +scalarTac -grind with Usize.add_spec as ⟨ix30, hix30⟩
  try
    have hixeq30 : ix30 = 3#usize := by scalar_tac
    subst ix30
  step +scalarTac -grind as ⟨acc30, hacc30⟩
  step +scalarTac -grind as ⟨l30, hl30⟩
  step +scalarTac -grind as ⟨r30, hr30⟩
  step +scalarTac -grind with kernel_mac_identity as ⟨pair30, h30⟩
  rcases pair30 with ⟨lo30, carry30⟩
  try dsimp only
  try simp only [Std.bind_assoc]
  step +scalarTac -grind as ⟨a30, ha30⟩
  step +scalarTac -grind with Usize.add_spec as ⟨j30, hj30⟩
  try
    have hjeq30 : j30 = 1#usize := by scalar_tac
    subst j30
  subst a30
  try simp only [bind_ok]
  rw [multiply_inner_unfold]
  unfold multiply_wide_loop0_loop0.body
  simp only [show (1#usize) < 4#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  step +scalarTac -grind with Usize.add_spec as ⟨ix31, hix31⟩
  try
    have hixeq31 : ix31 = 4#usize := by scalar_tac
    subst ix31
  step +scalarTac -grind as ⟨acc31, hacc31⟩
  step +scalarTac -grind as ⟨l31, hl31⟩
  step +scalarTac -grind as ⟨r31, hr31⟩
  step +scalarTac -grind with kernel_mac_identity as ⟨pair31, h31⟩
  rcases pair31 with ⟨lo31, carry31⟩
  try dsimp only
  try simp only [Std.bind_assoc]
  step +scalarTac -grind as ⟨a31, ha31⟩
  step +scalarTac -grind with Usize.add_spec as ⟨j31, hj31⟩
  try
    have hjeq31 : j31 = 2#usize := by scalar_tac
    subst j31
  subst a31
  try simp only [bind_ok]
  rw [multiply_inner_unfold]
  unfold multiply_wide_loop0_loop0.body
  simp only [show (2#usize) < 4#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  step +scalarTac -grind with Usize.add_spec as ⟨ix32, hix32⟩
  try
    have hixeq32 : ix32 = 5#usize := by scalar_tac
    subst ix32
  step +scalarTac -grind as ⟨acc32, hacc32⟩
  step +scalarTac -grind as ⟨l32, hl32⟩
  step +scalarTac -grind as ⟨r32, hr32⟩
  step +scalarTac -grind with kernel_mac_identity as ⟨pair32, h32⟩
  rcases pair32 with ⟨lo32, carry32⟩
  try dsimp only
  try simp only [Std.bind_assoc]
  step +scalarTac -grind as ⟨a32, ha32⟩
  step +scalarTac -grind with Usize.add_spec as ⟨j32, hj32⟩
  try
    have hjeq32 : j32 = 3#usize := by scalar_tac
    subst j32
  subst a32
  try simp only [bind_ok]
  rw [multiply_inner_unfold]
  unfold multiply_wide_loop0_loop0.body
  simp only [show (3#usize) < 4#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  step +scalarTac -grind with Usize.add_spec as ⟨ix33, hix33⟩
  try
    have hixeq33 : ix33 = 6#usize := by scalar_tac
    subst ix33
  step +scalarTac -grind as ⟨acc33, hacc33⟩
  step +scalarTac -grind as ⟨l33, hl33⟩
  step +scalarTac -grind as ⟨r33, hr33⟩
  step +scalarTac -grind with kernel_mac_identity as ⟨pair33, h33⟩
  rcases pair33 with ⟨lo33, carry33⟩
  try dsimp only
  try simp only [Std.bind_assoc]
  step +scalarTac -grind as ⟨a33, ha33⟩
  step +scalarTac -grind with Usize.add_spec as ⟨j33, hj33⟩
  try
    have hjeq33 : j33 = 4#usize := by scalar_tac
    subst j33
  subst a33
  try simp only [bind_ok]
  rw [multiply_inner_unfold]
  unfold multiply_wide_loop0_loop0.body
  simp only [show ¬ ((4#usize) < 4#usize) from by decide, ite_false, bind_ok]
  try dsimp only
  try simp only [bind_ok, Std.bind_assoc]
  step +scalarTac -grind with Usize.add_spec as ⟨upper3, hupper3⟩
  try
    have hupeq3 : upper3 = 7#usize := by scalar_tac
    subst upper3
  step +scalarTac -grind as ⟨outera3, houtera3⟩
  step +scalarTac -grind with Usize.add_spec as ⟨i3, hi3⟩
  try
    have hieq3 : i3 = 4#usize := by scalar_tac
    subst i3
  subst outera3
  try simp only [bind_ok]
  rw [multiply_outer_unfold]
  unfold multiply_wide_loop0.body
  simp only [show ¬ ((4#usize) < 4#usize) from by decide, ite_false, bind_ok]
  simp_all [val4, val8]
  norm_num [B, R] at *
  ring_nf at *
  omega

#print axioms multiply_wide_spec

end UdonVerify
