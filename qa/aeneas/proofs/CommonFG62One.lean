import CommonFG62Control
open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem fg_length_check_eq (len : Usize) (h : 1≤len.val ∧ len.val≤5) :
    core.ops.range.RangeInclusive.contains core.cmp.PartialOrdUsize
      core.cmp.PartialOrdUsize core.cmp.PartialOrdUsize ⟨1#usize,5#usize,false⟩ len=ok true := by
  simp [core.ops.range.RangeInclusive.contains,core.cmp.PartialOrdUsize,
    core.cmp.impls.PartialOrdUsize.le,liftFun2,h.1,h.2]

@[step]
theorem fg_one_spec (len : Usize) (f g : Signed62)
    (t : CommonFG62.field.pasta.safegcd.Trans2x2) (hl : len.val=1)
    (huv : |t.u.val|+|t.v.val|≤signedRadix)
    (hqr : |t.q.val|+|t.r.val|≤signedRadix)
    (hf : |f[0]!.val|≤signedRadix) (hg : |g[0]!.val|≤signedRadix)
    (hdivf : (t.u.val*f[0]!.val+t.v.val*g[0]!.val)%signedRadix=0)
    (hdivg : (t.q.val*f[0]!.val+t.r.val*g[0]!.val)%signedRadix=0) :
    CommonFG62.field.pasta.safegcd.update_fg_62_var len f g t ⦃ out =>
      out.1[0]!.val=(t.u.val*f[0]!.val+t.v.val*g[0]!.val)/signedRadix ∧
      out.2[0]!.val=(t.q.val*f[0]!.val+t.r.val*g[0]!.val)/signedRadix ∧
      (∀ k : Fin 5, 0<k.val → out.1[k.val]! = f[k.val]! ∧ out.2[k.val]! = g[k.val]!) ⦄ := by
  rw [fg_factored_bridge]
  unfold fgFactored
  simp only [core.ops.range.RangeInclusive.new,bind_ok]
  rw [fg_length_check_eq len (by omega)]
  simp only [bind_ok]
  step -grind
  step +scalarTac -grind as ⟨fi,hfi⟩
  step +scalarTac -grind as ⟨gi,hgi⟩
  have hfi0 : fi=f[0]! := by simpa [Array.getElem!_Nat_eq,f.property] using hfi
  have hgi0 : gi=g[0]! := by simpa [Array.getElem!_Nat_eq,g.property] using hgi
  step -grind with (fg_row_term_spec t.u t.v fi gi huv (by simpa [hfi0] using hf)
    (by simpa [hgi0] using hg)) as ⟨cf,hcf,hcbf⟩
  step -grind with (fg_row_term_spec t.q t.r fi gi hqr (by simpa [hfi0] using hf)
    (by simpa [hgi0] using hg)) as ⟨cg,hcg,hcbg⟩
  have hzf := fg_row_low_zero cf (by rw [hcf,hfi0,hgi0];exact hdivf)
  have hzg := fg_row_low_zero cg (by rw [hcg,hfi0,hgi0];exact hdivg)
  have hmask : CommonFG62.field.pasta.safegcd.MASK62=ok 4611686018427387903#u64 := by
    have hb : CommonFG62.field.pasta.safegcd.MASK62=Signed62Native.field.pasta.safegcd.MASK62 := by
      unfold CommonFG62.field.pasta.safegcd.MASK62 Signed62Native.field.pasta.safegcd.MASK62
      rfl
    exact hb.trans mask62_eq
  rw [hmask]
  simp only [lift,bind_ok]
  step -grind
  step -grind
  have hpos : 0≤signedRadix := by norm_num [signedRadix]
  step -grind with (fg_row_shift_spec cf (by omega))
    as ⟨cf1,hcf1,hcfb1⟩
  step -grind with (fg_row_shift_spec cg (by omega))
    as ⟨cg1,hcg1,hcgb1⟩
  step -grind with (core.iter.range.IteratorRange.next_Usize_none_spec
    { start:=1#usize, «end»:=len } (by simp [hl])) as ⟨opt,iter,hopt,hiter⟩
  simp only [hopt,lift,bind_ok]
  have hbackf := fg_row_tail_back cf1 hcfb1
  have hbackg := fg_row_tail_back cg1 hcgb1
  have hcastf := fg_row_tail_value cf1 hcfb1
  have hcastg := fg_row_tail_value cg1 hcgb1
  step -grind
  step -grind
  clear hbackf hbackg
  step +scalarTac -grind as ⟨last,hlast⟩
  have hlast0 : last.val=0 := by omega
  step +scalarTac -grind as ⟨outf,houtf⟩
  step +scalarTac -grind as ⟨outg,houtg⟩
  try simp only [WP.spec_ok]
  rw [houtf,houtg]
  refine ⟨?_,?_,?_⟩
  · rw [Array.getElem!_Nat_set_eq _ _ _ _ (by simp [hlast0])]
    rw [hcastf,hcf1,hcf,hfi0,hgi0]
  · rw [Array.getElem!_Nat_set_eq _ _ _ _ (by simp [hlast0])]
    rw [hcastg,hcg1,hcg,hfi0,hgi0]
  · intro k hk
    rw [Array.getElem!_Nat_set_ne _ _ _ _ (by omega),
      Array.getElem!_Nat_set_ne _ _ _ _ (by omega)]
    exact ⟨rfl,rfl⟩

#print axioms fg_length_check_eq
#print axioms fg_one_spec
end UdonVerify.CommonSigned62
