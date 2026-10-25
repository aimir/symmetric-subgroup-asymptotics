import SymmetricSubgroupAsymptotics.PrimitiveSoclePSLTwoProperSubnormalClassGap
import SymmetricSubgroupAsymptotics.PrimitiveSocleSmallHeadProperClassGap
import SymmetricSubgroupAsymptotics.PrimitiveSocleAlternatingProperSubnormalClassGap
import SymmetricSubgroupAsymptotics.CFSGTypeARankOneCardNine
import SymmetricSubgroupAsymptotics.CFSGPSLTwoCardFourAlternatingEquiv
import SymmetricSubgroupAsymptotics.CFSGPSLTwoCardFiveAlternatingEquiv
import SymmetricSubgroupAsymptotics.SimpleOrderThreeSixty
import SymmetricSubgroupAsymptotics.NonabelianSimpleProperIndex

/-! The literal four-, five- and nine-element fields complete the
proper-subnormal extra gap for every original PSL2 model. Field nine
uses only its actual order/class/outer metadata and faithful quotient;
field four reuses the proved literal Borel-coset equivalence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X]

theorem NonaffineData.proper_subnormal_class_cube_le_of_pslTwo_card_four
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order=4)
    (e : D.Simple ≃* CFSG.Models.A 1 q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.A 1 q) := e.symm.isSimpleGroup
  let E := CFSGPSLTwoCardFourAlternatingEquiv.equivAlternatingFive
    (F:=q.Field) (by simpa only [q.card_field] using hq)
  exact D.proper_subnormal_class_cube_le_of_alternating_component
    5 (by decide) (by decide) (e.trans E) H hH hne

theorem NonaffineData.proper_subnormal_class_cube_le_of_pslTwo_card_five
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order=5)
    (e : D.Simple ≃* CFSG.Models.A 1 q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  have hparams : q.prime=5 ∧ q.exponent=1 :=
    Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 5)
      q.exponent_pos.ne' (by decide : (1 : ℕ)≠0)
      (show q.prime^q.exponent=5^1 from hq)
  have hcmodel : Nat.card (ConjClasses (CFSG.Models.A 1 q)) ≤ 5 := by
    have h := CFSGTypeARankOneOddClassCube.twice_class_card_le q (by omega)
    omega
  have homodel : Nat.card (Outer (CFSG.Models.A 1 q)) ≤ 2 := by
    have h := CFSGPSLTwoOuterBound.typeA_rank_one_outer_card q
    omega
  refine D.proper_subnormal_class_cube_le_of_weak_class_cube_square 5 (by decide) ?_ ?_ ?_ H hH hne
  · exact nonabelianSimple_proper_index_five_le
      (fun h => D.noncommutative (isMulCommutative_iff.mpr h))
  · have hc : Nat.card (ConjClasses D.Simple) ≤ 5 :=
      (Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)).trans hcmodel
    have ho : Nat.card (Outer D.Simple) ≤ 2 := by
      rw [CFSGReduction.outer_card_congr e]
      exact homodel
    exact (Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3).trans (by decide)
  · have hs : Nat.card D.Simple=60 := (Nat.card_congr e.toEquiv).trans
      (CFSGPSLTwoCardFiveAlternatingEquiv.projective_card_eq_sixty
        (F:=q.Field) (by simpa only [q.card_field] using hq))
    rw [hs]
    decide

theorem NonaffineData.proper_subnormal_class_cube_le_of_pslTwo_card_nine
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order=9)
    (e : D.Simple ≃* CFSG.Models.A 1 q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.A 1 q) := e.symm.isSimpleGroup
  refine D.proper_subnormal_class_cube_le_of_small_model_head
    (CFSG.Models.A 1 q) e 6 360 7 4 (by decide)
    (CFSGTypeARankOneCardNine.card_eq q hq)
    (CFSGTypeARankOneCardNine.class_card_le q hq)
    (CFSGTypeARankOneCardNine.outer_card_le q hq)
    (SimpleOrderThreeSixty.proper_index_ge_six
      (CFSGTypeARankOneCardNine.card_eq q hq))
    (by decide) (by decide) (by decide) (by decide) (by decide) H hH hne

theorem NonaffineData.proper_subnormal_class_cube_le_of_pslTwo_all_fields
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : 4 ≤ q.order)
    (e : D.Simple ≃* CFSG.Models.A 1 q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  rcases D.proper_subnormal_class_cube_or_pslTwo_three_fields q hq e H hH hne with hc | hfour | hfive | hnine
  · exact hc
  · exact D.proper_subnormal_class_cube_le_of_pslTwo_card_four q hfour e H hH hne
  · exact D.proper_subnormal_class_cube_le_of_pslTwo_card_five q hfive e H hH hne
  · exact D.proper_subnormal_class_cube_le_of_pslTwo_card_nine q hnine e H hH hne

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
