import Pratt
import NativeArithmetic

namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

theorem prime_2 : Nat.Prime 2 := by norm_num

theorem prime_3 : Nat.Prime 3 := by norm_num

theorem prime_5 : Nat.Prime 5 := by norm_num

theorem prime_7 : Nat.Prime 7 := by norm_num

theorem prime_11 : Nat.Prime 11 := by norm_num

theorem prime_13 : Nat.Prime 13 := by norm_num

theorem prime_17 : Nat.Prime 17 := by norm_num

theorem prime_19 : Nat.Prime 19 := by norm_num

theorem prime_23 : Nat.Prime 23 := by norm_num

theorem prime_29 : Nat.Prime 29 := by norm_num

theorem prime_41 : Nat.Prime 41 := by norm_num

theorem prime_43 : Nat.Prime 43 := by norm_num

theorem prime_53 : Nat.Prime 53 := by norm_num

theorem prime_59 : Nat.Prime 59 := by norm_num

theorem prime_71 : Nat.Prime 71 := by norm_num

theorem prime_89 : Nat.Prime 89 := by norm_num

theorem prime_173 : Nat.Prime 173 := by norm_num

theorem prime_241 : Nat.Prime 241 := by norm_num

theorem prime_359 : Nat.Prime 359 := by norm_num

theorem prime_463 : Nat.Prime 463 := by norm_num

theorem prime_509 : Nat.Prime 509 := by norm_num

theorem prime_757 : Nat.Prime 757 := by norm_num

theorem prime_827 : Nat.Prime 827 := by norm_num

theorem prime_829 : Nat.Prime 829 := by norm_num

theorem prime_977 : Nat.Prime 977 := by norm_num

theorem prime_1381 : Nat.Prime 1381 := by norm_num

theorem prime_1709 : Nat.Prime 1709 := by norm_num

theorem prime_1973 : Nat.Prime 1973 := by norm_num

theorem prime_2531 : Nat.Prime 2531 := by norm_num

theorem prime_2557 : Nat.Prime 2557 := by norm_num

theorem prime_3037 : Nat.Prime 3037 := by norm_num

theorem prime_3767 : Nat.Prime 3767 := by norm_num

theorem prime_6091 : Nat.Prime 6091 := by norm_num

theorem prime_6229 : Nat.Prime 6229 := by norm_num

theorem prime_12149 : Nat.Prime 12149 := by
  apply UdonVerify.lucas_list_prime 12149 2 [2, 2, 3037]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl
    all_goals first | exact prime_2 | exact prime_3037
  · have h : UdonVerify.powMod 12149 2 (12149 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl
    · have h : UdonVerify.powMod 12149 2 ((12149 - 1) / 2) = 12148 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 12149 2 ((12149 - 1) / 3037) = 16 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_14923 : Nat.Prime 14923 := by
  apply UdonVerify.lucas_list_prime 14923 2 [2, 3, 3, 829]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_829
  · have h : UdonVerify.powMod 14923 2 (14923 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl
    · have h : UdonVerify.powMod 14923 2 ((14923 - 1) / 2) = 14922 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 14923 2 ((14923 - 1) / 3) = 10689 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 14923 2 ((14923 - 1) / 829) = 8453 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_19267 : Nat.Prime 19267 := by
  apply UdonVerify.lucas_list_prime 19267 3 [2, 3, 13, 13, 19]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_13 | exact prime_19
  · have h : UdonVerify.powMod 19267 3 (19267 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · have h : UdonVerify.powMod 19267 3 ((19267 - 1) / 2) = 19266 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 19267 3 ((19267 - 1) / 3) = 7149 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 19267 3 ((19267 - 1) / 13) = 17399 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 19267 3 ((19267 - 1) / 19) = 11161 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_24859 : Nat.Prime 24859 := by
  apply UdonVerify.lucas_list_prime 24859 2 [2, 3, 3, 1381]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_1381
  · have h : UdonVerify.powMod 24859 2 (24859 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl
    · have h : UdonVerify.powMod 24859 2 ((24859 - 1) / 2) = 24858 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 24859 2 ((24859 - 1) / 3) = 3141 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 24859 2 ((24859 - 1) / 1381) = 13554 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_24917 : Nat.Prime 24917 := by
  apply UdonVerify.lucas_list_prime 24917 2 [2, 2, 6229]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl
    all_goals first | exact prime_2 | exact prime_6229
  · have h : UdonVerify.powMod 24917 2 (24917 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl
    · have h : UdonVerify.powMod 24917 2 ((24917 - 1) / 2) = 24916 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 24917 2 ((24917 - 1) / 6229) = 16 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_25741 : Nat.Prime 25741 := by
  apply UdonVerify.lucas_list_prime 25741 6 [2, 2, 3, 3, 5, 11, 13]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_5 | exact prime_11 | exact prime_13
  · have h : UdonVerify.powMod 25741 6 (25741 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · have h : UdonVerify.powMod 25741 6 ((25741 - 1) / 2) = 25740 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 25741 6 ((25741 - 1) / 3) = 24210 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 25741 6 ((25741 - 1) / 5) = 2525 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 25741 6 ((25741 - 1) / 11) = 21223 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 25741 6 ((25741 - 1) / 13) = 12350 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_31649 : Nat.Prime 31649 := by
  apply UdonVerify.lucas_list_prime 31649 3 [2, 2, 2, 2, 2, 23, 43]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_23 | exact prime_43
  · have h : UdonVerify.powMod 31649 3 (31649 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl
    · have h : UdonVerify.powMod 31649 3 ((31649 - 1) / 2) = 31648 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 31649 3 ((31649 - 1) / 23) = 14720 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 31649 3 ((31649 - 1) / 43) = 14756 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_68477 : Nat.Prime 68477 := by
  apply UdonVerify.lucas_list_prime 68477 2 [2, 2, 17, 19, 53]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_17 | exact prime_19 | exact prime_53
  · have h : UdonVerify.powMod 68477 2 (68477 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · have h : UdonVerify.powMod 68477 2 ((68477 - 1) / 2) = 68476 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 68477 2 ((68477 - 1) / 17) = 31138 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 68477 2 ((68477 - 1) / 19) = 60450 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 68477 2 ((68477 - 1) / 53) = 67194 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_115603 : Nat.Prime 115603 := by
  apply UdonVerify.lucas_list_prime 115603 2 [2, 3, 19267]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_19267
  · have h : UdonVerify.powMod 115603 2 (115603 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl
    · have h : UdonVerify.powMod 115603 2 ((115603 - 1) / 2) = 115602 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 115603 2 ((115603 - 1) / 3) = 57631 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 115603 2 ((115603 - 1) / 19267) = 64 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_125803 : Nat.Prime 125803 := by
  apply UdonVerify.lucas_list_prime 125803 3 [2, 3, 3, 29, 241]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_29 | exact prime_241
  · have h : UdonVerify.powMod 125803 3 (125803 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · have h : UdonVerify.powMod 125803 3 ((125803 - 1) / 2) = 125802 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 125803 3 ((125803 - 1) / 3) = 3383 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 125803 3 ((125803 - 1) / 29) = 96997 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 125803 3 ((125803 - 1) / 241) = 39603 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_149503 : Nat.Prime 149503 := by
  apply UdonVerify.lucas_list_prime 149503 3 [2, 3, 24917]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_24917
  · have h : UdonVerify.powMod 149503 3 (149503 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl
    · have h : UdonVerify.powMod 149503 3 ((149503 - 1) / 2) = 149502 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 149503 3 ((149503 - 1) / 3) = 17235 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 149503 3 ((149503 - 1) / 24917) = 729 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_294793 : Nat.Prime 294793 := by
  apply UdonVerify.lucas_list_prime 294793 10 [2, 2, 2, 3, 71, 173]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_71 | exact prime_173
  · have h : UdonVerify.powMod 294793 10 (294793 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · have h : UdonVerify.powMod 294793 10 ((294793 - 1) / 2) = 294792 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 294793 10 ((294793 - 1) / 3) = 176588 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 294793 10 ((294793 - 1) / 71) = 262006 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 294793 10 ((294793 - 1) / 173) = 212929 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_413527 : Nat.Prime 413527 := by
  apply UdonVerify.lucas_list_prime 413527 3 [2, 3, 41, 41, 41]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_41
  · have h : UdonVerify.powMod 413527 3 (413527 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl
    · have h : UdonVerify.powMod 413527 3 ((413527 - 1) / 2) = 413526 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 413527 3 ((413527 - 1) / 3) = 120035 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 413527 3 ((413527 - 1) / 41) = 362589 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_772231 : Nat.Prime 772231 := by
  apply UdonVerify.lucas_list_prime 772231 6 [2, 3, 5, 25741]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_5 | exact prime_25741
  · have h : UdonVerify.powMod 772231 6 (772231 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · have h : UdonVerify.powMod 772231 6 ((772231 - 1) / 2) = 772230 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 772231 6 ((772231 - 1) / 3) = 339746 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 772231 6 ((772231 - 1) / 5) = 516799 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 772231 6 ((772231 - 1) / 25741) = 20949 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_897019 : Nat.Prime 897019 := by
  apply UdonVerify.lucas_list_prime 897019 2 [2, 3, 149503]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_149503
  · have h : UdonVerify.powMod 897019 2 (897019 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl
    · have h : UdonVerify.powMod 897019 2 ((897019 - 1) / 2) = 897018 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 897019 2 ((897019 - 1) / 3) = 125837 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 897019 2 ((897019 - 1) / 149503) = 64 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_958679 : Nat.Prime 958679 := by
  apply UdonVerify.lucas_list_prime 958679 7 [2, 7, 68477]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_7 | exact prime_68477
  · have h : UdonVerify.powMod 958679 7 (958679 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl
    · have h : UdonVerify.powMod 958679 7 ((958679 - 1) / 2) = 958678 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 958679 7 ((958679 - 1) / 7) = 512666 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 958679 7 ((958679 - 1) / 68477) = 820904 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_1197907 : Nat.Prime 1197907 := by
  apply UdonVerify.lucas_list_prime 1197907 3 [2, 3, 53, 3767]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_53 | exact prime_3767
  · have h : UdonVerify.powMod 1197907 3 (1197907 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · have h : UdonVerify.powMod 1197907 3 ((1197907 - 1) / 2) = 1197906 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 1197907 3 ((1197907 - 1) / 3) = 71795 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 1197907 3 ((1197907 - 1) / 53) = 596032 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 1197907 3 ((1197907 - 1) / 3767) = 65324 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_2012849 : Nat.Prime 2012849 := by
  apply UdonVerify.lucas_list_prime 2012849 3 [2, 2, 2, 2, 125803]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl
    all_goals first | exact prime_2 | exact prime_125803
  · have h : UdonVerify.powMod 2012849 3 (2012849 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl
    · have h : UdonVerify.powMod 2012849 3 ((2012849 - 1) / 2) = 2012848 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 2012849 3 ((2012849 - 1) / 125803) = 776892 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_4025699 : Nat.Prime 4025699 := by
  apply UdonVerify.lucas_list_prime 4025699 2 [2, 2012849]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl
    all_goals first | exact prime_2 | exact prime_2012849
  · have h : UdonVerify.powMod 4025699 2 (4025699 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl
    · have h : UdonVerify.powMod 4025699 2 ((4025699 - 1) / 2) = 4025698 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 4025699 2 ((4025699 - 1) / 2012849) = 4 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_4229279 : Nat.Prime 4229279 := by
  apply UdonVerify.lucas_list_prime 4229279 13 [2, 827, 2557]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_827 | exact prime_2557
  · have h : UdonVerify.powMod 4229279 13 (4229279 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl
    · have h : UdonVerify.powMod 4229279 13 ((4229279 - 1) / 2) = 4229278 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 4229279 13 ((4229279 - 1) / 827) = 1929961 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 4229279 13 ((4229279 - 1) / 2557) = 2896247 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_5701177 : Nat.Prime 5701177 := by
  apply UdonVerify.lucas_list_prime 5701177 7 [2, 2, 2, 3, 3, 13, 6091]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_13 | exact prime_6091
  · have h : UdonVerify.powMod 5701177 7 (5701177 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · have h : UdonVerify.powMod 5701177 7 ((5701177 - 1) / 2) = 5701176 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 5701177 7 ((5701177 - 1) / 3) = 1594751 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 5701177 7 ((5701177 - 1) / 13) = 3596688 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 5701177 7 ((5701177 - 1) / 6091) = 579280 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_6942563 : Nat.Prime 6942563 := by
  apply UdonVerify.lucas_list_prime 6942563 2 [2, 11, 17, 19, 977]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_11 | exact prime_17 | exact prime_19 | exact prime_977
  · have h : UdonVerify.powMod 6942563 2 (6942563 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · have h : UdonVerify.powMod 6942563 2 ((6942563 - 1) / 2) = 6942562 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 6942563 2 ((6942563 - 1) / 11) = 1142703 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 6942563 2 ((6942563 - 1) / 17) = 6280446 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 6942563 2 ((6942563 - 1) / 19) = 1534969 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 6942563 2 ((6942563 - 1) / 977) = 5061822 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_41655379 : Nat.Prime 41655379 := by
  apply UdonVerify.lucas_list_prime 41655379 2 [2, 3, 6942563]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_6942563
  · have h : UdonVerify.powMod 41655379 2 (41655379 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl
    · have h : UdonVerify.powMod 41655379 2 ((41655379 - 1) / 2) = 41655378 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 41655379 2 ((41655379 - 1) / 3) = 18196789 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 41655379 2 ((41655379 - 1) / 6942563) = 64 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_80513981 : Nat.Prime 80513981 := by
  apply UdonVerify.lucas_list_prime 80513981 2 [2, 2, 5, 4025699]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_5 | exact prime_4025699
  · have h : UdonVerify.powMod 80513981 2 (80513981 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl
    · have h : UdonVerify.powMod 80513981 2 ((80513981 - 1) / 2) = 80513980 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 80513981 2 ((80513981 - 1) / 5) = 56308228 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 80513981 2 ((80513981 - 1) / 4025699) = 1048576 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_399082391 : Nat.Prime 399082391 := by
  apply UdonVerify.lucas_list_prime 399082391 7 [2, 5, 7, 5701177]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_5 | exact prime_7 | exact prime_5701177
  · have h : UdonVerify.powMod 399082391 7 (399082391 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · have h : UdonVerify.powMod 399082391 7 ((399082391 - 1) / 2) = 399082390 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 399082391 7 ((399082391 - 1) / 5) = 256110654 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 399082391 7 ((399082391 - 1) / 7) = 384547542 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 399082391 7 ((399082391 - 1) / 5701177) = 176673839 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_4129989133 : Nat.Prime 4129989133 := by
  apply UdonVerify.lucas_list_prime 4129989133 5 [2, 2, 3, 359, 958679]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_359 | exact prime_958679
  · have h : UdonVerify.powMod 4129989133 5 (4129989133 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · have h : UdonVerify.powMod 4129989133 5 ((4129989133 - 1) / 2) = 4129989132 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 4129989133 5 ((4129989133 - 1) / 3) = 602717201 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 4129989133 5 ((4129989133 - 1) / 359) = 2911702230 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 4129989133 5 ((4129989133 - 1) / 958679) = 3687147883 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_22160661629 : Nat.Prime 22160661629 := by
  apply UdonVerify.lucas_list_prime 22160661629 3 [2, 2, 7, 19, 41655379]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_7 | exact prime_19 | exact prime_41655379
  · have h : UdonVerify.powMod 22160661629 3 (22160661629 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · have h : UdonVerify.powMod 22160661629 3 ((22160661629 - 1) / 2) = 22160661628 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 22160661629 3 ((22160661629 - 1) / 7) = 4941799706 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 22160661629 3 ((22160661629 - 1) / 19) = 17941852505 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 22160661629 3 ((22160661629 - 1) / 41655379) = 10852739022 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_417677162933 : Nat.Prime 417677162933 := by
  apply UdonVerify.lucas_list_prime 417677162933 2 [2, 2, 59, 1973, 897019]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_59 | exact prime_1973 | exact prime_897019
  · have h : UdonVerify.powMod 417677162933 2 (417677162933 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · have h : UdonVerify.powMod 417677162933 2 ((417677162933 - 1) / 2) = 417677162932 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 417677162933 2 ((417677162933 - 1) / 59) = 217323280587 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 417677162933 2 ((417677162933 - 1) / 1973) = 138627498251 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 417677162933 2 ((417677162933 - 1) / 897019) = 379604725915 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_5239247429827 : Nat.Prime 5239247429827 := by
  apply UdonVerify.lucas_list_prime 5239247429827 2 [2, 3, 3, 757, 12149, 31649]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_757 | exact prime_12149 | exact prime_31649
  · have h : UdonVerify.powMod 5239247429827 2 (5239247429827 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · have h : UdonVerify.powMod 5239247429827 2 ((5239247429827 - 1) / 2) = 5239247429826 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 5239247429827 2 ((5239247429827 - 1) / 3) = 5086662601473 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 5239247429827 2 ((5239247429827 - 1) / 757) = 2628659820580 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 5239247429827 2 ((5239247429827 - 1) / 12149) = 1185373242847 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 5239247429827 2 ((5239247429827 - 1) / 31649) = 1269557927592 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_5247740253619 : Nat.Prime 5247740253619 := by
  apply UdonVerify.lucas_list_prime 5247740253619 2 [2, 3, 3, 3, 17, 71, 80513981]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_17 | exact prime_71 | exact prime_80513981
  · have h : UdonVerify.powMod 5247740253619 2 (5247740253619 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · have h : UdonVerify.powMod 5247740253619 2 ((5247740253619 - 1) / 2) = 5247740253618 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 5247740253619 2 ((5247740253619 - 1) / 3) = 3100194221930 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 5247740253619 2 ((5247740253619 - 1) / 17) = 4103874968942 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 5247740253619 2 ((5247740253619 - 1) / 71) = 5046144227130 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 5247740253619 2 ((5247740253619 - 1) / 80513981) = 93740937873 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_325086459374267 : Nat.Prime 325086459374267 := by
  apply UdonVerify.lucas_list_prime 325086459374267 2 [2, 509, 413527, 772231]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_509 | exact prime_413527 | exact prime_772231
  · have h : UdonVerify.powMod 325086459374267 2 (325086459374267 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · have h : UdonVerify.powMod 325086459374267 2 ((325086459374267 - 1) / 2) = 325086459374266 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 325086459374267 2 ((325086459374267 - 1) / 509) = 129472211388361 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 325086459374267 2 ((325086459374267 - 1) / 413527) = 102008102706872 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 325086459374267 2 ((325086459374267 - 1) / 772231) = 156180095894647 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_539204044132271846773 : Nat.Prime 539204044132271846773 := by
  apply UdonVerify.lucas_list_prime 539204044132271846773 5 [2, 2, 3, 3, 3, 3, 3, 89, 14923, 417677162933]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_89 | exact prime_14923 | exact prime_417677162933
  · have h : UdonVerify.powMod 539204044132271846773 5 (539204044132271846773 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · have h : UdonVerify.powMod 539204044132271846773 5 ((539204044132271846773 - 1) / 2) = 539204044132271846772 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 539204044132271846773 5 ((539204044132271846773 - 1) / 3) = 72181157461130002303 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 539204044132271846773 5 ((539204044132271846773 - 1) / 89) = 438828511890509762189 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 539204044132271846773 5 ((539204044132271846773 - 1) / 14923) = 294085405607369123303 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 539204044132271846773 5 ((539204044132271846773 - 1) / 417677162933) = 355094899067762221197 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_1690502597179744445941507 : Nat.Prime 1690502597179744445941507 := by
  apply UdonVerify.lucas_list_prime 1690502597179744445941507 2 [2, 3, 13, 4129989133, 5247740253619]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_13 | exact prime_4129989133 | exact prime_5247740253619
  · have h : UdonVerify.powMod 1690502597179744445941507 2 (1690502597179744445941507 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · have h : UdonVerify.powMod 1690502597179744445941507 2 ((1690502597179744445941507 - 1) / 2) = 1690502597179744445941506 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 1690502597179744445941507 2 ((1690502597179744445941507 - 1) / 3) = 245744272243721259157177 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 1690502597179744445941507 2 ((1690502597179744445941507 - 1) / 13) = 1575639655108145965203126 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 1690502597179744445941507 2 ((1690502597179744445941507 - 1) / 4129989133) = 996072215982464255939398 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 1690502597179744445941507 2 ((1690502597179744445941507 - 1) / 5247740253619) = 1660222743337851280110475 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_10427374428728808478656897599072717 : Nat.Prime 10427374428728808478656897599072717 := by
  apply UdonVerify.lucas_list_prime 10427374428728808478656897599072717 2 [2, 2, 294793, 4229279, 399082391, 5239247429827]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_294793 | exact prime_4229279 | exact prime_399082391 | exact prime_5239247429827
  · have h : UdonVerify.powMod 10427374428728808478656897599072717 2 (10427374428728808478656897599072717 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · have h : UdonVerify.powMod 10427374428728808478656897599072717 2 ((10427374428728808478656897599072717 - 1) / 2) = 10427374428728808478656897599072716 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 10427374428728808478656897599072717 2 ((10427374428728808478656897599072717 - 1) / 294793) = 141030142704377787764626290196987 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 10427374428728808478656897599072717 2 ((10427374428728808478656897599072717 - 1) / 4229279) = 80641114290502549749304143711569 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 10427374428728808478656897599072717 2 ((10427374428728808478656897599072717 - 1) / 399082391) = 8608077744952143376646591648751451 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 10427374428728808478656897599072717 2 ((10427374428728808478656897599072717 - 1) / 5239247429827) = 3927780385925492675817601106173530 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_8999194758858563409123804352480028797519453 : Nat.Prime 8999194758858563409123804352480028797519453 := by
  apply UdonVerify.lucas_list_prime 8999194758858563409123804352480028797519453 2 [2, 2, 3, 3, 3, 3, 11, 2531, 115603, 1197907, 22160661629, 325086459374267]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_11 | exact prime_2531 | exact prime_115603 | exact prime_1197907 | exact prime_22160661629 | exact prime_325086459374267
  · have h : UdonVerify.powMod 8999194758858563409123804352480028797519453 2 (8999194758858563409123804352480028797519453 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h : UdonVerify.powMod 8999194758858563409123804352480028797519453 2 ((8999194758858563409123804352480028797519453 - 1) / 2) = 8999194758858563409123804352480028797519452 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 8999194758858563409123804352480028797519453 2 ((8999194758858563409123804352480028797519453 - 1) / 3) = 6517330866429466181348555905887869997045656 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 8999194758858563409123804352480028797519453 2 ((8999194758858563409123804352480028797519453 - 1) / 11) = 813623623551915197479703713311836623485267 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 8999194758858563409123804352480028797519453 2 ((8999194758858563409123804352480028797519453 - 1) / 2531) = 1833280879400548462489020109479889992188016 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 8999194758858563409123804352480028797519453 2 ((8999194758858563409123804352480028797519453 - 1) / 115603) = 5381518379154031554051565032301077920065244 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 8999194758858563409123804352480028797519453 2 ((8999194758858563409123804352480028797519453 - 1) / 1197907) = 3201522544944086055076342566780970077300245 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 8999194758858563409123804352480028797519453 2 ((8999194758858563409123804352480028797519453 - 1) / 22160661629) = 7468371576130240648439236849311461678235198 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 8999194758858563409123804352480028797519453 2 ((8999194758858563409123804352480028797519453 - 1) / 325086459374267) = 1923835525255145170976080895073905971702885 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_28948022309329048855892746252171976963363056481941560715954676764349967630337 : Nat.Prime 28948022309329048855892746252171976963363056481941560715954676764349967630337 := by
  apply UdonVerify.lucas_list_prime 28948022309329048855892746252171976963363056481941560715954676764349967630337 5 [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 463, 539204044132271846773, 8999194758858563409123804352480028797519453]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_463 | exact prime_539204044132271846773 | exact prime_8999194758858563409123804352480028797519453
  · have h : UdonVerify.powMod 28948022309329048855892746252171976963363056481941560715954676764349967630337 5 (28948022309329048855892746252171976963363056481941560715954676764349967630337 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · have h : UdonVerify.powMod 28948022309329048855892746252171976963363056481941560715954676764349967630337 5 ((28948022309329048855892746252171976963363056481941560715954676764349967630337 - 1) / 2) = 28948022309329048855892746252171976963363056481941560715954676764349967630336 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 28948022309329048855892746252171976963363056481941560715954676764349967630337 5 ((28948022309329048855892746252171976963363056481941560715954676764349967630337 - 1) / 3) = 20444556541222657078399132219657928148671392403212669005631716460534733845831 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 28948022309329048855892746252171976963363056481941560715954676764349967630337 5 ((28948022309329048855892746252171976963363056481941560715954676764349967630337 - 1) / 463) = 21130164847715179260305574026050308433852420324783633235003921985597389212508 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 28948022309329048855892746252171976963363056481941560715954676764349967630337 5 ((28948022309329048855892746252171976963363056481941560715954676764349967630337 - 1) / 539204044132271846773) = 12708223814453757661368674774463026954997156495664362173913458310178886824313 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 28948022309329048855892746252171976963363056481941560715954676764349967630337 5 ((28948022309329048855892746252171976963363056481941560715954676764349967630337 - 1) / 8999194758858563409123804352480028797519453) = 26481904113327098742228215817454532048648008744346411596057084665402439738326 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem prime_28948022309329048855892746252171976963363056481941647379679742748393362948097 : Nat.Prime 28948022309329048855892746252171976963363056481941647379679742748393362948097 := by
  apply UdonVerify.lucas_list_prime 28948022309329048855892746252171976963363056481941647379679742748393362948097 5 [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 1709, 24859, 1690502597179744445941507, 10427374428728808478656897599072717]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_2 | exact prime_3 | exact prime_1709 | exact prime_24859 | exact prime_1690502597179744445941507 | exact prime_10427374428728808478656897599072717
  · have h : UdonVerify.powMod 28948022309329048855892746252171976963363056481941647379679742748393362948097 5 (28948022309329048855892746252171976963363056481941647379679742748393362948097 - 1) = 1 := by decide
    simpa only [Nat.cast_one] using UdonVerify.powMod_zmod (by norm_num) h
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left, or_self] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · have h : UdonVerify.powMod 28948022309329048855892746252171976963363056481941647379679742748393362948097 5 ((28948022309329048855892746252171976963363056481941647379679742748393362948097 - 1) / 2) = 28948022309329048855892746252171976963363056481941647379679742748393362948096 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 28948022309329048855892746252171976963363056481941647379679742748393362948097 5 ((28948022309329048855892746252171976963363056481941647379679742748393362948097 - 1) / 3) = 2942865608506852014473558576493638302197734138389222805617480874486368177743 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 28948022309329048855892746252171976963363056481941647379679742748393362948097 5 ((28948022309329048855892746252171976963363056481941647379679742748393362948097 - 1) / 1709) = 7222445436716077817085455829064676966066432888710940026805849237043540165474 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 28948022309329048855892746252171976963363056481941647379679742748393362948097 5 ((28948022309329048855892746252171976963363056481941647379679742748393362948097 - 1) / 24859) = 2691341377366259037456412615546252060488528530710384847859062312656176693819 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 28948022309329048855892746252171976963363056481941647379679742748393362948097 5 ((28948022309329048855892746252171976963363056481941647379679742748393362948097 - 1) / 1690502597179744445941507) = 133965301011675531377011136732371344562481153598085042558526552447273737781 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval
    · have h : UdonVerify.powMod 28948022309329048855892746252171976963363056481941647379679742748393362948097 5 ((28948022309329048855892746252171976963363056481941647379679742748393362948097 - 1) / 10427374428728808478656897599072717) = 1788360732791938138902184365512038798442399290337140366210748154819109629358 := by decide
      rw [UdonVerify.powMod_zmod (by norm_num) h]
      intro heq
      have hval := (ZMod.natCast_eq_natCast_iff' _ 1 _).mp heq
      norm_num at hval

theorem fp_prime : Nat.Prime fpPrime := by
  have h : fpPrime = 28948022309329048855892746252171976963363056481941560715954676764349967630337 := by
    norm_num [fpPrime, fpParameters, val4, R, B,
      udon_kernel_slice.field.pasta.PallasBase.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS]
  rw [h]
  exact prime_28948022309329048855892746252171976963363056481941560715954676764349967630337

#print axioms fp_prime

theorem fq_prime : Nat.Prime fqPrime := by
  have h : fqPrime = 28948022309329048855892746252171976963363056481941647379679742748393362948097 := by
    norm_num [fqPrime, fqParameters, val4, R, B,
      udon_kernel_slice.field.pasta.PallasScalar.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS]
  rw [h]
  exact prime_28948022309329048855892746252171976963363056481941647379679742748393362948097

#print axioms fq_prime

end UdonVerify.Native
