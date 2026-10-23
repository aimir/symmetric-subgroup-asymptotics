import SymmetricSubgroupAsymptotics.PrimitiveSocleAlternatingProductClassBound

/-! The actual alternating simple square-index inequality also pays the
raw regular/diagonal power degree form. Consequently the checked
factorial-product budget covers at least two alternating socle factors
at EVERY degree, for every original subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X:Type}[Group G][Finite G][Finite X][MulAction G X]

theorem NonaffineData.subgroup_class_cube_le_of_alternating_power_form
    (D:NonaffineData G X)(m:ℕ)(hm : 5  ≤  m)(e:D.Simple≃*alternatingGroup (Fin m))
    (hk : 2  ≤  D.factorCount)(a:ℕ)(hka : D.factorCount  ≤  2*a)
    (hdegree:Nat.card X=Nat.card D.Simple ^ a)(H:Subgroup G) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X-1) := by
  have hs:m ^ 2 ≤ Nat.card D.Simple :=
    (CFSGAlternatingMinimumIndex.degree_square_lt_card m hm).le.trans_eq
      (Nat.card_congr e.toEquiv).symm
  have hdegreeLower:m ^ D.factorCount ≤ Nat.card X := by
    calc
      m ^ D.factorCount ≤ m ^ (2*a) := Nat.pow_le_pow_right (by omega) hka
      _=(m ^ 2) ^ a := pow_mul _ _ _
      _ ≤ Nat.card D.Simple ^ a := Nat.pow_le_pow_left hs a
      _=Nat.card X := hdegree.symm
  have hc:Nat.card (ConjClasses H) ≤ (2*m.factorial) ^ D.factorCount*D.factorCount.factorial :=
    (Nat.card_le_card_of_surjective (@ConjClasses.mk H _) ConjClasses.mk_surjective).trans
      (H.card_le_card_group.trans (D.card_le_alternating_product m hm e))
  exact (Nat.pow_le_pow_left hc 3).trans
    ((AlternatingSocleProductOrderNumerics.factorial_product_cube m D.factorCount hm hk).trans
      (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hdegreeLower 1)))

theorem NonaffineData.subgroup_class_cube_le_of_alternating_multiple_factors_all_degrees
    (D:NonaffineData G X)(m:ℕ)(hm : 5  ≤  m)(e:D.Simple≃*alternatingGroup (Fin m))
    (hk : 2  ≤  D.factorCount)(H:Subgroup G) : Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X-1) := by
  rcases D.indexForm with ⟨K,hK,hdegree⟩|⟨a,hka,hdegree⟩
  · exact D.subgroup_class_cube_le_of_alternating_index_form m hm e hk K hK hdegree H
  · exact D.subgroup_class_cube_le_of_alternating_power_form m hm e hk a hka hdegree H

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
