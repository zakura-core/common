import NativeChainSteps
import NativeCanonical

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem fp_sqrt_chain_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (inverse : Nat)
    (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (value : Element M Loose) (hvalue : val4 value.limbs < 2 * val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.parameters.ParametersPallasBasePallasBase.pow_sqrt_exponent.__bento_chain
      (NativeField.zakura_udon.field.pasta.parameters.Power.Insts.Zakura_bento_coreAddchainAdditionChain inst) value
      ⦃ out => val4 out.limbs < 2 * val4 params.modulus ∧
        decode (val4 params.modulus) inverse out.limbs =
          decode (val4 params.modulus) inverse value.limbs ^ (((fpPrime - 1) / 2 ^ 32 - 1) / 2) % val4 params.modulus ⦄ := by
  let base := decode (val4 params.modulus) inverse value.limbs
  have hb0 := hvalue
  have hp0 : decode (val4 params.modulus) inverse value.limbs = base ^ 1 % val4 params.modulus := by
    simp only [base, pow_one, decode, Nat.mod_mod]
  unfold NativeField.zakura_udon.field.pasta.parameters.ParametersPallasBasePallasBase.pow_sqrt_exponent.__bento_chain
  simp only [NativeField.core.mem.drop, bind_ok]
  step -grind with (chain_double_n_spec inst params inverse hinverse base value 1 1#usize hb0 hp0)
    as ⟨v1, hb1, hp1⟩
  change decode (val4 params.modulus) inverse v1.limbs = base ^ 2 % val4 params.modulus at hp1
  step -grind with (chain_add_spec inst params inverse hinverse base value v1 1 2 hb0 hb1 hp0 hp1)
    as ⟨v2, hb2, hp2⟩
  change decode (val4 params.modulus) inverse v2.limbs = base ^ 3 % val4 params.modulus at hp2
  step -grind with (chain_add_spec inst params inverse hinverse base v2 v1 3 2 hb2 hb1 hp2 hp1)
    as ⟨v3, hb3, hp3⟩
  change decode (val4 params.modulus) inverse v3.limbs = base ^ 5 % val4 params.modulus at hp3
  step -grind with (chain_add_spec inst params inverse hinverse base v3 v1 5 2 hb3 hb1 hp3 hp1)
    as ⟨v4, hb4, hp4⟩
  change decode (val4 params.modulus) inverse v4.limbs = base ^ 7 % val4 params.modulus at hp4
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base value value 1 1 129#usize hb0 hb0 hp0 hp0)
    as ⟨v6, hb6, hp6⟩
  change decode (val4 params.modulus) inverse v6.limbs = base ^ 680564733841876926926749214863536422913 % val4 params.modulus at hp6
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v6 value 680564733841876926926749214863536422913 1 4#usize hb6 hb0 hp6 hp0)
    as ⟨v8, hb8, hp8⟩
  change decode (val4 params.modulus) inverse v8.limbs = base ^ 10889035741470030830827987437816582766609 % val4 params.modulus at hp8
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v8 value 10889035741470030830827987437816582766609 1 3#usize hb8 hb0 hp8 hp0)
    as ⟨v10, hb10, hp10⟩
  change decode (val4 params.modulus) inverse v10.limbs = base ^ 87112285931760246646623899502532662132873 % val4 params.modulus at hp10
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v10 v2 87112285931760246646623899502532662132873 3 5#usize hb10 hb2 hp10 hp2)
    as ⟨v12, hb12, hp12⟩
  change decode (val4 params.modulus) inverse v12.limbs = base ^ 2787593149816327892691964784081045188251939 % val4 params.modulus at hp12
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v12 value 2787593149816327892691964784081045188251939 1 2#usize hb12 hb0 hp12 hp0)
    as ⟨v14, hb14, hp14⟩
  change decode (val4 params.modulus) inverse v14.limbs = base ^ 11150372599265311570767859136324180753007757 % val4 params.modulus at hp14
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v14 v2 11150372599265311570767859136324180753007757 3 4#usize hb14 hb2 hp14 hp2)
    as ⟨v16, hb16, hp16⟩
  change decode (val4 params.modulus) inverse v16.limbs = base ^ 178405961588244985132285746181186892048124115 % val4 params.modulus at hp16
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v16 v4 178405961588244985132285746181186892048124115 7 6#usize hb16 hb4 hp16 hp4)
    as ⟨v18, hb18, hp18⟩
  change decode (val4 params.modulus) inverse v18.limbs = base ^ 11417981541647679048466287755595961091079943367 % val4 params.modulus at hp18
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v18 v4 11417981541647679048466287755595961091079943367 7 3#usize hb18 hb4 hp18 hp4)
    as ⟨v20, hb20, hp20⟩
  change decode (val4 params.modulus) inverse v20.limbs = base ^ 91343852333181432387730302044767688728639546943 % val4 params.modulus at hp20
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v20 value 91343852333181432387730302044767688728639546943 1 7#usize hb20 hb0 hp20 hp0)
    as ⟨v22, hb22, hp22⟩
  change decode (val4 params.modulus) inverse v22.limbs = base ^ 11692013098647223345629478661730264157265862008705 % val4 params.modulus at hp22
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v22 v3 11692013098647223345629478661730264157265862008705 5 5#usize hb22 hb3 hp22 hp3)
    as ⟨v24, hb24, hp24⟩
  change decode (val4 params.modulus) inverse v24.limbs = base ^ 374144419156711147060143317175368453032507584278565 % val4 params.modulus at hp24
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v24 v2 374144419156711147060143317175368453032507584278565 3 4#usize hb24 hb2 hp24 hp2)
    as ⟨v26, hb26, hp26⟩
  change decode (val4 params.modulus) inverse v26.limbs = base ^ 5986310706507378352962293074805895248520121348457043 % val4 params.modulus at hp26
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v26 v4 5986310706507378352962293074805895248520121348457043 7 5#usize hb26 hb4 hp26 hp4)
    as ⟨v28, hb28, hp28⟩
  change decode (val4 params.modulus) inverse v28.limbs = base ^ 191561942608236107294793378393788647952643883150625383 % val4 params.modulus at hp28
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v28 v2 191561942608236107294793378393788647952643883150625383 3 2#usize hb28 hb2 hp28 hp2)
    as ⟨v30, hb30, hp30⟩
  change decode (val4 params.modulus) inverse v30.limbs = base ^ 766247770432944429179173513575154591810575532602501535 % val4 params.modulus at hp30
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v30 value 766247770432944429179173513575154591810575532602501535 1 3#usize hb30 hb0 hp30 hp0)
    as ⟨v32, hb32, hp32⟩
  change decode (val4 params.modulus) inverse v32.limbs = base ^ 6129982163463555433433388108601236734484604260820012281 % val4 params.modulus at hp32
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v32 v2 6129982163463555433433388108601236734484604260820012281 3 5#usize hb32 hb2 hp32 hp2)
    as ⟨v34, hb34, hp34⟩
  change decode (val4 params.modulus) inverse v34.limbs = base ^ 196159429230833773869868419475239575503507336346240392995 % val4 params.modulus at hp34
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v34 v4 196159429230833773869868419475239575503507336346240392995 7 4#usize hb34 hb4 hp34 hp4)
    as ⟨v36, hb36, hp36⟩
  change decode (val4 params.modulus) inverse v36.limbs = base ^ 3138550867693340381917894711603833208056117381539846287927 % val4 params.modulus at hp36
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v36 v2 3138550867693340381917894711603833208056117381539846287927 3 4#usize hb36 hb2 hp36 hp2)
    as ⟨v38, hb38, hp38⟩
  change decode (val4 params.modulus) inverse v38.limbs = base ^ 50216813883093446110686315385661331328897878104637540606835 % val4 params.modulus at hp38
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v38 value 50216813883093446110686315385661331328897878104637540606835 1 3#usize hb38 hb0 hp38 hp0)
    as ⟨v40, hb40, hp40⟩
  change decode (val4 params.modulus) inverse v40.limbs = base ^ 401734511064747568885490523085290650631183024837100324854681 % val4 params.modulus at hp40
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v40 v3 401734511064747568885490523085290650631183024837100324854681 5 5#usize hb40 hb3 hp40 hp3)
    as ⟨v42, hb42, hp42⟩
  change decode (val4 params.modulus) inverse v42.limbs = base ^ 12855504354071922204335696738729300820197856794787210395349797 % val4 params.modulus at hp42
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v42 v3 12855504354071922204335696738729300820197856794787210395349797 5 3#usize hb42 hb3 hp42 hp3)
    as ⟨v44, hb44, hp44⟩
  change decode (val4 params.modulus) inverse v44.limbs = base ^ 102844034832575377634685573909834406561582854358297683162798381 % val4 params.modulus at hp44
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v44 v2 102844034832575377634685573909834406561582854358297683162798381 3 4#usize hb44 hb2 hp44 hp2)
    as ⟨v46, hb46, hp46⟩
  change decode (val4 params.modulus) inverse v46.limbs = base ^ 1645504557321206042154969182557350504985325669732762930604774099 % val4 params.modulus at hp46
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v46 v4 1645504557321206042154969182557350504985325669732762930604774099 7 7#usize hb46 hb4 hp46 hp4)
    as ⟨v48, hb48, hp48⟩
  change decode (val4 params.modulus) inverse v48.limbs = base ^ 210624583337114373395836055367340864638121685725793655117411084679 % val4 params.modulus at hp48
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v48 v2 210624583337114373395836055367340864638121685725793655117411084679 3 3#usize hb48 hb2 hp48 hp2)
    as ⟨v50, hb50, hp50⟩
  change decode (val4 params.modulus) inverse v50.limbs = base ^ 1684996666696914987166688442938726917104973485806349240939288677435 % val4 params.modulus at hp50
  step -grind with (chain_double_n_spec inst params inverse hinverse base v50 1684996666696914987166688442938726917104973485806349240939288677435 1#usize hb50 hp50)
    as ⟨v51, hb51, hp51⟩
  change decode (val4 params.modulus) inverse v51.limbs = base ^ 3369993333393829974333376885877453834209946971612698481878577354870 % val4 params.modulus at hp51
  refine ⟨hb51, ?_⟩
  have he : (3369993333393829974333376885877453834209946971612698481878577354870 : Nat) = ((fpPrime - 1) / 2 ^ 32 - 1) / 2 := by
    with_unfolding_all decide
  simpa only [he] using hp51

#print axioms fp_sqrt_chain_spec

@[step]
theorem fq_sqrt_chain_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (inverse : Nat)
    (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (value : Element M Loose) (hvalue : val4 value.limbs < 2 * val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.parameters.ParametersPallasScalarPallasScalar.pow_sqrt_exponent.__bento_chain
      (NativeField.zakura_udon.field.pasta.parameters.Power.Insts.Zakura_bento_coreAddchainAdditionChain inst) value
      ⦃ out => val4 out.limbs < 2 * val4 params.modulus ∧
        decode (val4 params.modulus) inverse out.limbs =
          decode (val4 params.modulus) inverse value.limbs ^ (((fqPrime - 1) / 2 ^ 32 - 1) / 2) % val4 params.modulus ⦄ := by
  let base := decode (val4 params.modulus) inverse value.limbs
  have hb0 := hvalue
  have hp0 : decode (val4 params.modulus) inverse value.limbs = base ^ 1 % val4 params.modulus := by
    simp only [base, pow_one, decode, Nat.mod_mod]
  unfold NativeField.zakura_udon.field.pasta.parameters.ParametersPallasScalarPallasScalar.pow_sqrt_exponent.__bento_chain
  simp only [NativeField.core.mem.drop, bind_ok]
  step -grind with (chain_double_n_spec inst params inverse hinverse base value 1 1#usize hb0 hp0)
    as ⟨v1, hb1, hp1⟩
  change decode (val4 params.modulus) inverse v1.limbs = base ^ 2 % val4 params.modulus at hp1
  step -grind with (chain_add_spec inst params inverse hinverse base value v1 1 2 hb0 hb1 hp0 hp1)
    as ⟨v2, hb2, hp2⟩
  change decode (val4 params.modulus) inverse v2.limbs = base ^ 3 % val4 params.modulus at hp2
  step -grind with (chain_add_spec inst params inverse hinverse base v2 v1 3 2 hb2 hb1 hp2 hp1)
    as ⟨v3, hb3, hp3⟩
  change decode (val4 params.modulus) inverse v3.limbs = base ^ 5 % val4 params.modulus at hp3
  step -grind with (chain_add_spec inst params inverse hinverse base v3 v1 5 2 hb3 hb1 hp3 hp1)
    as ⟨v4, hb4, hp4⟩
  change decode (val4 params.modulus) inverse v4.limbs = base ^ 7 % val4 params.modulus at hp4
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base value value 1 1 129#usize hb0 hb0 hp0 hp0)
    as ⟨v6, hb6, hp6⟩
  change decode (val4 params.modulus) inverse v6.limbs = base ^ 680564733841876926926749214863536422913 % val4 params.modulus at hp6
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v6 value 680564733841876926926749214863536422913 1 4#usize hb6 hb0 hp6 hp0)
    as ⟨v8, hb8, hp8⟩
  change decode (val4 params.modulus) inverse v8.limbs = base ^ 10889035741470030830827987437816582766609 % val4 params.modulus at hp8
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v8 value 10889035741470030830827987437816582766609 1 3#usize hb8 hb0 hp8 hp0)
    as ⟨v10, hb10, hp10⟩
  change decode (val4 params.modulus) inverse v10.limbs = base ^ 87112285931760246646623899502532662132873 % val4 params.modulus at hp10
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v10 v2 87112285931760246646623899502532662132873 3 5#usize hb10 hb2 hp10 hp2)
    as ⟨v12, hb12, hp12⟩
  change decode (val4 params.modulus) inverse v12.limbs = base ^ 2787593149816327892691964784081045188251939 % val4 params.modulus at hp12
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v12 value 2787593149816327892691964784081045188251939 1 2#usize hb12 hb0 hp12 hp0)
    as ⟨v14, hb14, hp14⟩
  change decode (val4 params.modulus) inverse v14.limbs = base ^ 11150372599265311570767859136324180753007757 % val4 params.modulus at hp14
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v14 v2 11150372599265311570767859136324180753007757 3 4#usize hb14 hb2 hp14 hp2)
    as ⟨v16, hb16, hp16⟩
  change decode (val4 params.modulus) inverse v16.limbs = base ^ 178405961588244985132285746181186892048124115 % val4 params.modulus at hp16
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v16 v4 178405961588244985132285746181186892048124115 7 6#usize hb16 hb4 hp16 hp4)
    as ⟨v18, hb18, hp18⟩
  change decode (val4 params.modulus) inverse v18.limbs = base ^ 11417981541647679048466287755595961091079943367 % val4 params.modulus at hp18
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v18 v4 11417981541647679048466287755595961091079943367 7 3#usize hb18 hb4 hp18 hp4)
    as ⟨v20, hb20, hp20⟩
  change decode (val4 params.modulus) inverse v20.limbs = base ^ 91343852333181432387730302044767688728639546943 % val4 params.modulus at hp20
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v20 value 91343852333181432387730302044767688728639546943 1 7#usize hb20 hb0 hp20 hp0)
    as ⟨v22, hb22, hp22⟩
  change decode (val4 params.modulus) inverse v22.limbs = base ^ 11692013098647223345629478661730264157265862008705 % val4 params.modulus at hp22
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v22 v2 11692013098647223345629478661730264157265862008705 3 4#usize hb22 hb2 hp22 hp2)
    as ⟨v24, hb24, hp24⟩
  change decode (val4 params.modulus) inverse v24.limbs = base ^ 187072209578355573530071658587684226516253792139283 % val4 params.modulus at hp24
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v24 v3 187072209578355573530071658587684226516253792139283 5 5#usize hb24 hb3 hp24 hp3)
    as ⟨v26, hb26, hp26⟩
  change decode (val4 params.modulus) inverse v26.limbs = base ^ 5986310706507378352962293074805895248520121348457061 % val4 params.modulus at hp26
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v26 v3 5986310706507378352962293074805895248520121348457061 5 5#usize hb26 hb3 hp26 hp3)
    as ⟨v28, hb28, hp28⟩
  change decode (val4 params.modulus) inverse v28.limbs = base ^ 191561942608236107294793378393788647952643883150625957 % val4 params.modulus at hp28
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v28 value 191561942608236107294793378393788647952643883150625957 1 2#usize hb28 hb0 hp28 hp0)
    as ⟨v30, hb30, hp30⟩
  change decode (val4 params.modulus) inverse v30.limbs = base ^ 766247770432944429179173513575154591810575532602503829 % val4 params.modulus at hp30
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v30 v2 766247770432944429179173513575154591810575532602503829 3 5#usize hb30 hb2 hp30 hp2)
    as ⟨v32, hb32, hp32⟩
  change decode (val4 params.modulus) inverse v32.limbs = base ^ 24519928653854221733733552434404946937938417043280122531 % val4 params.modulus at hp32
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v32 v4 24519928653854221733733552434404946937938417043280122531 7 4#usize hb32 hb4 hp32 hp4)
    as ⟨v34, hb34, hp34⟩
  change decode (val4 params.modulus) inverse v34.limbs = base ^ 392318858461667547739736838950479151007014672692481960503 % val4 params.modulus at hp34
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v34 v2 392318858461667547739736838950479151007014672692481960503 3 3#usize hb34 hb2 hp34 hp2)
    as ⟨v36, hb36, hp36⟩
  change decode (val4 params.modulus) inverse v36.limbs = base ^ 3138550867693340381917894711603833208056117381539855684027 % val4 params.modulus at hp36
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v36 v2 3138550867693340381917894711603833208056117381539855684027 3 5#usize hb36 hb2 hp36 hp2)
    as ⟨v38, hb38, hp38⟩
  change decode (val4 params.modulus) inverse v38.limbs = base ^ 100433627766186892221372630771322662657795756209275381888867 % val4 params.modulus at hp38
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v38 value 100433627766186892221372630771322662657795756209275381888867 1 4#usize hb38 hb0 hp38 hp0)
    as ⟨v40, hb40, hp40⟩
  change decode (val4 params.modulus) inverse v40.limbs = base ^ 1606938044258990275541962092341162602524732099348406110221873 % val4 params.modulus at hp40
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v40 v2 1606938044258990275541962092341162602524732099348406110221873 3 5#usize hb40 hb2 hp40 hp2)
    as ⟨v42, hb42, hp42⟩
  change decode (val4 params.modulus) inverse v42.limbs = base ^ 51422017416287688817342786954917203280791427179148995527099939 % val4 params.modulus at hp42
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v42 v4 51422017416287688817342786954917203280791427179148995527099939 7 4#usize hb42 hb4 hp42 hp4)
    as ⟨v44, hb44, hp44⟩
  change decode (val4 params.modulus) inverse v44.limbs = base ^ 822752278660603021077484591278675252492662834866383928433599031 % val4 params.modulus at hp44
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v44 v3 822752278660603021077484591278675252492662834866383928433599031 5 4#usize hb44 hb3 hp44 hp3)
    as ⟨v46, hb46, hp46⟩
  change decode (val4 params.modulus) inverse v46.limbs = base ^ 13164036458569648337239753460458804039882605357862142854937584501 % val4 params.modulus at hp46
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v46 value 13164036458569648337239753460458804039882605357862142854937584501 1 1#usize hb46 hb0 hp46 hp0)
    as ⟨v48, hb48, hp48⟩
  change decode (val4 params.modulus) inverse v48.limbs = base ^ 26328072917139296674479506920917608079765210715724285709875169003 % val4 params.modulus at hp48
  step -grind with (chain_double_n_add_spec inst params inverse hinverse base v48 value 26328072917139296674479506920917608079765210715724285709875169003 1 3#usize hb48 hb0 hp48 hp0)
    as ⟨v50, hb50, hp50⟩
  change decode (val4 params.modulus) inverse v50.limbs = base ^ 210624583337114373395836055367340864638121685725794285679001352025 % val4 params.modulus at hp50
  step -grind with (chain_double_n_spec inst params inverse hinverse base v50 210624583337114373395836055367340864638121685725794285679001352025 4#usize hb50 hp50)
    as ⟨v51, hb51, hp51⟩
  change decode (val4 params.modulus) inverse v51.limbs = base ^ 3369993333393829974333376885877453834209946971612708570864021632400 % val4 params.modulus at hp51
  refine ⟨hb51, ?_⟩
  have he : (3369993333393829974333376885877453834209946971612708570864021632400 : Nat) = ((fqPrime - 1) / 2 ^ 32 - 1) / 2 := by
    with_unfolding_all decide
  simpa only [he] using hp51

#print axioms fq_sqrt_chain_spec

@[step]
theorem fp_pow_sqrt_exponent_spec (value : Element Base Loose)
    (hvalue : val4 value.limbs < 2 * fpPrime) :
    NativeField.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.pow_sqrt_exponent value
      ⦃ out => val4 out.limbs < 2 * fpPrime ∧
        decode fpPrime fpRadixInverse out.limbs =
          decode fpPrime fpRadixInverse value.limbs ^ (((fpPrime - 1) / 2 ^ 32 - 1) / 2) % fpPrime ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.pow_sqrt_exponent
  simpa only [fp_native_prime_eq] using
    fp_sqrt_chain_spec fpNativeInst fpNativeParameters fpRadixInverse fp_radix_inverse value hvalue

@[step]
theorem fq_pow_sqrt_exponent_spec (value : Element Scalar Loose)
    (hvalue : val4 value.limbs < 2 * fqPrime) :
    NativeField.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.pow_sqrt_exponent value
      ⦃ out => val4 out.limbs < 2 * fqPrime ∧
        decode fqPrime fqRadixInverse out.limbs =
          decode fqPrime fqRadixInverse value.limbs ^ (((fqPrime - 1) / 2 ^ 32 - 1) / 2) % fqPrime ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.pow_sqrt_exponent
  simpa only [fq_native_prime_eq] using
    fq_sqrt_chain_spec fqNativeInst fqNativeParameters fqRadixInverse fq_radix_inverse value hvalue

#print axioms fp_pow_sqrt_exponent_spec
#print axioms fq_pow_sqrt_exponent_spec

end UdonVerify.Native
