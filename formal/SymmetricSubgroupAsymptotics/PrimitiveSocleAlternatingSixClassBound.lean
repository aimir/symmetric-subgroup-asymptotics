import SymmetricSubgroupAsymptotics.PrimitiveSocleAlternatingSingleFactorClassBound
import SymmetricSubgroupAsymptotics.AlternatingSixNaturalActionClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleSubnormalClassBound
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The exceptional A6 automorphisms are retained. At degree six the
original faithful permutation representation has image A6 or S6. Degree
seven is impossible from the literal subgroup-index/cardinality degree
form. At every larger degree the actual seven-class and outer-four
bounds pay the cube budget. No classification of small subgroups occurs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

private theorem alternating_six_card : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  have hh := two_mul_nat_card_alternatingGroup (α := Fin 6)
  rw [Nat.card_perm, Nat.card_fin] at hh
  change 2 * Nat.card (alternatingGroup (Fin 6)) = 720 at hh
  omega

theorem NonaffineData.alternating_six_degree_ne_seven
    (D : NonaffineData G X) (e : D.Simple ≃* alternatingGroup (Fin 6))
    (hk : D.factorCount = 1) : Nat.card X ≠ 7 := by
  have hc : Nat.card D.Simple = 360 := (Nat.card_congr e.toEquiv).trans alternating_six_card
  intro hn
  rcases D.indexForm with ⟨K, _, hdegree⟩ | ⟨a, hka, hdegree⟩
  · rw [hk, pow_one, hn] at hdegree
    have hmul := K.card_mul_index
    rw [←hdegree, hc] at hmul
    omega
  · have ha : a ≠ 0 := by omega
    rw [hc, hn] at hdegree
    have hlarge := Nat.le_self_pow ha 360
    rw [←hdegree] at hlarge
    omega

theorem NonaffineData.subnormal_class_card_le_alternating_six
    (D : NonaffineData G X) (e : D.Simple ≃* alternatingGroup (Fin 6))
    (hk : D.factorCount = 1) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ≤ 28 := by
  have hs : Nat.card (ConjClasses D.Simple) ≤ 7 :=
    (Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)).trans
        AlternatingSixClassBound.alternating_six_class_card_le_seven
  have ho : Nat.card (Outer D.Simple) ≤ 4 := by
    rw [CFSGReduction.outer_card_congr e]
    exact CFSGAlternatingOuterBound.outer_card_le_four 6 (by decide)
  exact (D.subnormal_class_card_le_of_factor_one hk H hH).trans
    (by simpa only [show 7 * 4 = 28 by decide] using Nat.mul_le_mul hs ho)

theorem NonaffineData.subnormal_class_cube_le_alternating_six_degree_six
    [FaithfulSMul G X] (D : NonaffineData G X)
    (e : D.Simple ≃* alternatingGroup (Fin 6)) (hk : D.factorCount = 1)
    (hn : Nat.card X = 6) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ 5 := by
  let a : X ≃ Fin 6 := Finite.equivFinOfCardEq hn
  let f : G →* Equiv.Perm (Fin 6) :=
    a.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G X)
  have hf : Function.Injective f :=
    a.permCongrHom.injective.comp MulAction.toPerm_injective
  have hN : Nat.card (finiteGroupSocle G) = 360 :=
    (Nat.card_congr ((D.oneFactorEquiv hk).trans e).toEquiv).trans alternating_six_card
  exact AlternatingSixNaturalActionClassBound.class_cube_le
    (finiteGroupSocle G) hN f hf H hH

theorem NonaffineData.subnormal_class_cube_le_of_alternating_six_all_degrees
    [FaithfulSMul G X] (D : NonaffineData G X)
    (e : D.Simple ≃* alternatingGroup (Fin 6)) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 1) := by
  by_cases hk : 2 ≤ D.factorCount
  · exact D.subgroup_class_cube_le_of_alternating_multiple_factors_all_degrees 6 (by decide) e hk H
  have hk1 : D.factorCount = 1 := by have hp := D.factorCount_pos; omega
  have hlo := D.degree_lower_alternating 6 (by decide) e
  have hn7 := D.alternating_six_degree_ne_seven e hk1
  by_cases hn6 : Nat.card X = 6
  · simpa only [hn6] using D.subnormal_class_cube_le_alternating_six_degree_six e hk1 hn6 H hH
  have hn8 : 8 ≤ Nat.card X := by omega
  exact (Nat.pow_le_pow_left (D.subnormal_class_card_le_alternating_six e hk1 H hH) 3).trans
    ((show 28 ^ 3 ≤ 5 ^ 7 by decide).trans
      (Nat.pow_le_pow_right (by decide) (by omega : 7 ≤ Nat.card X - 1)))

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
