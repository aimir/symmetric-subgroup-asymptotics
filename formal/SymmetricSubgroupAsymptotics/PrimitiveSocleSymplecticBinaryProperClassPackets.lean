import SymmetricSubgroupAsymptotics.PrimitiveSocleSymplecticLiteralProperCapacity
import SymmetricSubgroupAsymptotics.PrimitiveSocleSymplecticBinaryHigherRankClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleSymplecticBinaryPointRankFourClassBound

/-! The same actual characteristic-two two-frame and point-radical
indices pay the proper-subnormal reserve. Literal symplectic endpoints
also retain simplicity from any later actual type-B equivalence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction CFSGSymplecticSerreMatrices
open SymplecticEvenHigherSiegelNumerics SymplecticTwoFrameIndexNumerics
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.proper_subnormal_class_cube_le_of_symplectic_binary_higher_literal
    (D : NonaffineData G X) (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (hprime : q.prime=2) (e : D.Simple ≃* elementaryProjective q.Field r)
    (hwindow : 4 ≤ q.order ∨ 5 ≤ r)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (elementaryProjective q.Field r) := e.symm.isSimpleGroup
  letI : CharP q.Field 2 := by rw [← hprime]; infer_instance
  have hraw : ∀ K : Subgroup (elementaryProjective q.Field r), K ≠ ⊤ →
      (q.order-1)*q.order^(r-2)*(q.order^r-q.order) ≤ 2*K.index := by
    intro K hK
    obtain ⟨m,rfl⟩ : ∃ m : ℕ, r=m+1 := ⟨r-1,by omega⟩
    simpa only [q.card_field,show m+1-2=m-1 by omega] using
      CFSGSymplecticBinaryHigherSiegelIndex.projective_two_frame_le_two_mul_proper_index
        q.Field m (by omega) K hK
  by_cases hq4 : 4 ≤ q.order
  · exact D.proper_subnormal_class_cube_le_of_symplectic_literal_budget
      r hr q e (q.order^(2*r-2)) (field_four_power_ge_thirtyTwo q.order r hq4 hr)
      (fun K hK => field_four_power_le q.order r K.index hq4 hr (hraw K hK))
      (field_four_order_cube q.order r hq4 hr) H hH hne
  · have hr5 : 5 ≤ r := hwindow.resolve_left hq4
    have he : q.exponent=1 := by
      by_contra hh
      have htwo : 2 ≤ q.exponent := by have := q.exponent_pos; omega
      apply hq4
      change 4 ≤ q.prime^q.exponent
      rw [hprime]
      exact Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) htwo
    have hq2 : q.order=2 := by
      change q.prime^q.exponent=2
      rw [hprime,he,pow_one]
    refine D.proper_subnormal_class_cube_le_of_symplectic_literal_budget
      r hr q e (binaryIndexLower r) (binary_ge_thirtyTwo r hr5) ?_ ?_ H hH hne
    · intro K hK
      have hb := hraw K hK
      rw [hq2] at hb
      exact binary_power_le r K.index hr hb
    · simpa only [hq2] using binary_order_cube r hr5

theorem NonaffineData.proper_subnormal_class_cube_le_of_typeC_binary_higher_rank
    (D : NonaffineData G X) (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (hprime : q.prime=2) (e : D.Simple ≃* CFSG.Models.C r q)
    (hwindow : 4 ≤ q.order ∨ 5 ≤ r)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.C r q) := e.symm.isSimpleGroup
  obtain ⟨s,rfl⟩ : ∃ s : ℕ, r=s+3 := ⟨r-3,by omega⟩
  let c := serreProjectiveEquivElementaryProjective q.Field (s+2)
  exact D.proper_subnormal_class_cube_le_of_symplectic_binary_higher_literal
    (s+3) hr q hprime (e.trans c) hwindow H hH hne

theorem NonaffineData.proper_subnormal_class_cube_le_of_symplectic_binary_point_rank_four_literal
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order=2)
    (e : D.Simple ≃* elementaryProjective q.Field 4)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  have hprime : q.prime=2 := by
    have h := Nat.le_self_pow q.exponent_pos.ne' q.prime
    have hlo := q.prime_isPrime.two_le
    change q.prime ≤ q.order at h
    omega
  letI : CharP q.Field 2 := by rw [← hprime]; infer_instance
  letI : IsSimpleGroup (elementaryProjective q.Field 4) := e.symm.isSimpleGroup
  apply D.proper_subnormal_class_cube_le_of_symplectic_literal_budget
    4 (by omega) q e 56 (by omega) _ _ H hH hne
  · intro K hK
    have h := CFSGSymplecticBinaryPointIndex.binary_point_radical_proper_index
      q.Field (q.card_field.trans hq) 4 (by omega) K hK
    norm_num at h
    exact h
  · rw [hq]
    norm_num

theorem NonaffineData.proper_subnormal_class_cube_le_of_typeC_binary_point_rank_four
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order=2)
    (e : D.Simple ≃* CFSG.Models.C 4 q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.C 4 q) := e.symm.isSimpleGroup
  exact D.proper_subnormal_class_cube_le_of_symplectic_binary_point_rank_four_literal q hq
    (e.trans (serreProjectiveEquivElementaryProjective q.Field 3)) H hH hne

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
