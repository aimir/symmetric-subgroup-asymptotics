import SymmetricSubgroupAsymptotics.CFSGSymplecticSmallClassBounds
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPointIndex
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryRankTwoSharpIndex
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBCharTwoProjectiveEquiv
import SymmetricSubgroupAsymptotics.CFSGSymplecticOuterCardinality
import SymmetricSubgroupAsymptotics.CFSGSymplecticLeastIndexSquare
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsParameters
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawChart
import SymmetricSubgroupAsymptotics.PrimitiveSocleModelClassCubeSquareClassBound

/-! The actual primary class codes close the binary rank-three B/C
models and the four-element-field rank-two C model. Original subnormal
subgroups, all socle factors and both original degree forms are retained.
No class table or additional class-count hypothesis is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction CFSGSymplecticSerreMatrices
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

private theorem two_parameters (q : CFSG.PrimePower) (hq : q.order = 2) :
    q.prime = 2 ∧ q.exponent = 1 :=
  Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 2)
    q.exponent_pos.ne' (by decide : (1 : ℕ) ≠ 0)
    (show q.prime^q.exponent = 2^1 from hq)

private theorem four_parameters (q : CFSG.PrimePower) (hq : q.order = 4) :
    q.prime = 2 ∧ q.exponent = 2 :=
  Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 2)
    q.exponent_pos.ne' (by decide : (2 : ℕ) ≠ 0)
    (show q.prime^q.exponent = 2^2 from hq)

private theorem quotient_class_card_le (K : Type) [Field K] [Finite K] (r : ℕ) :
    Nat.card (ConjClasses (elementaryProjective K r)) ≤
      Nat.card (ConjClasses (elementaryRootGroup K r)) := by
  let f := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K r))
  exact Nat.card_le_card_of_surjective (ConjClasses.map f)
    (ConjClasses.map_surjective (QuotientGroup.mk'_surjective _))

theorem NonaffineData.subnormal_class_cube_le_of_binary_rank_three_literal
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order = 2)
    (e : D.Simple ≃* elementaryProjective q.Field 3) (H : Subgroup G)
    (hH : H.IsSubnormal) : Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  have hpar := two_parameters q hq
  letI : CharP q.Field 2 := by rw [←hpar.1]; infer_instance
  letI : IsSimpleGroup (elementaryProjective q.Field 3) := e.symm.isSimpleGroup
  letI : Finite (elementaryProjective q.Field 3) := Finite.of_equiv D.Simple e.toEquiv
  have hc : Nat.card (ConjClasses (elementaryProjective q.Field 3)) ≤ 96 :=
    (quotient_class_card_le q.Field 3).trans
      (CFSGSymplecticSmallClassBounds.binary_rankThree q.Field (q.card_field.trans hq))
  have ho : Nat.card (Outer (elementaryProjective q.Field 3)) ≤ 3 := by
    have h := CFSGSymplecticPointRootLabels.binary_outer_card_le (K := q.Field) 2 (by decide)
    simpa only [CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q,hpar.2,mul_one] using h
  have hi (K : Subgroup (elementaryProjective q.Field 3)) (hK : K ≠ ⊤) : 12 ≤ K.index := by
    have h := CFSGSymplecticBinaryPointIndex.binary_point_radical_proper_index
      q.Field (q.card_field.trans hq) 3 (by decide) K hK
    norm_num at h
    exact h
  have hsquare : 12^2 ≤ Nat.card (elementaryProjective q.Field 3) := by
    obtain ⟨ell,hell⟩ := exists_leastProperIndex (elementaryProjective q.Field 3)
    obtain ⟨K,hK,he⟩ := hell.1
    have hlo : 12 ≤ ell := (hi K hK).trans_eq he
    have hs := elementary_leastProperIndex_square_lt_card q.Field 2 (by decide)
      (by omega) ell hell
    exact (Nat.pow_le_pow_left hlo 2).trans hs.le
  apply D.subnormal_class_cube_le_of_model_capacity
    (elementaryProjective q.Field 3) e 12 (by decide) hi _ hsquare H hH
  exact (Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3).trans (by decide)

theorem NonaffineData.subnormal_class_cube_le_of_four_rank_two_literal
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order = 4)
    (e : D.Simple ≃* elementaryProjective q.Field 2) (H : Subgroup G)
    (hH : H.IsSubnormal) : Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  have hpar := four_parameters q hq
  letI : CharP q.Field 2 := by rw [←hpar.1]; infer_instance
  letI : IsSimpleGroup (elementaryProjective q.Field 2) := e.symm.isSimpleGroup
  letI : Finite (elementaryProjective q.Field 2) := Finite.of_equiv D.Simple e.toEquiv
  have hc : Nat.card (ConjClasses (elementaryProjective q.Field 2)) ≤ 192 :=
    (quotient_class_card_le q.Field 2).trans
      (CFSGSymplecticSmallClassBounds.four_rankTwo q.Field (q.card_field.trans hq))
  have ho : Nat.card (Outer (elementaryProjective q.Field 2)) ≤ 6 := by
    have h := CFSGSymplecticPointRootLabels.binary_outer_card_le (K := q.Field) 1 (by decide)
    simpa only [CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q,hpar.2] using h
  have hi (K : Subgroup (elementaryProjective q.Field 2)) (hK : K ≠ ⊤) : 18 ≤ K.index := by
    have h := CFSGSymplecticBinaryRankTwoSharpIndex.projective_field_mul_square_sub_one_le_twice_proper_index
      q.Field K hK
    rw [q.card_field,hq] at h
    norm_num at h
    omega
  have hsquare : 18^2 ≤ Nat.card (elementaryProjective q.Field 2) := by
    obtain ⟨ell,hell⟩ := exists_leastProperIndex (elementaryProjective q.Field 2)
    obtain ⟨K,hK,he⟩ := hell.1
    have hlo : 18 ≤ ell := (hi K hK).trans_eq he
    have hs := elementary_leastProperIndex_square_lt_card q.Field 1 (by decide)
      (by rw [q.card_field,hq]; decide) ell hell
    exact (Nat.pow_le_pow_left hlo 2).trans hs.le
  apply D.subnormal_class_cube_le_of_model_capacity
    (elementaryProjective q.Field 2) e 18 (by decide) hi _ hsquare H hH
  exact (Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3).trans (by decide)

theorem NonaffineData.subnormal_class_cube_le_of_typeC_binary_rank_three
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order = 2)
    (e : D.Simple ≃* CFSG.Models.C 3 q) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.C 3 q) := e.symm.isSimpleGroup
  exact D.subnormal_class_cube_le_of_binary_rank_three_literal q hq
    (e.trans (serreProjectiveEquivElementaryProjective q.Field 2)) H hH

theorem NonaffineData.subnormal_class_cube_le_of_typeB_binary_rank_three
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order = 2)
    (e : D.Simple ≃* CFSG.Models.B 3 q) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  have hpar := two_parameters q hq
  letI : CharP q.Field 2 := by rw [←hpar.1]; infer_instance
  letI : IsSimpleGroup (CFSG.Models.B 3 q) := e.symm.isSimpleGroup
  exact D.subnormal_class_cube_le_of_binary_rank_three_literal q hq
    (e.trans (CFSGOrthogonalBSerreMatrices.serreProjectiveEquivSymplecticProjective_charTwo
      q.Field 2 (by decide))) H hH

theorem NonaffineData.subnormal_class_cube_le_of_typeC_four_rank_two
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order = 4)
    (e : D.Simple ≃* CFSG.Models.C 2 q) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.C 2 q) := e.symm.isSimpleGroup
  exact D.subnormal_class_cube_le_of_four_rank_two_literal q hq
    (e.trans (serreProjectiveEquivElementaryProjective q.Field 1)) H hH

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
