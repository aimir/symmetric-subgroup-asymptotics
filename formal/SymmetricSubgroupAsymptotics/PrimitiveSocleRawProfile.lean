import SymmetricSubgroupAsymptotics.PrimitiveSocleRawOneFactor
import SymmetricSubgroupAsymptotics.NonabelianSimpleProperIndex
import SymmetricSubgroupAsymptotics.PrimitiveBoundedCataloguePublishedLocator

/-! Construct the quantitative profile from bare O'Nan--Scott data and the
separate ordinary simple-index inequalities. One factor uses the regular
action and exact order of the ORIGINAL quotient, not the full outer group. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open Non2UnipotentPrefixFiniteMenu OuterWreathPermutationCompression

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

def NonaffineData.exactProfile (D : NonaffineData G X)
    (hindex : PublishedSimpleIndexBounds) :
    ExactPrimitiveSemisimpleOuterLogProfile G (Nat.card X) := by
  let ell := Classical.choose (exists_leastProperIndex D.Simple)
  have hell : LeastProperIndex D.Simple ell :=
    Classical.choose_spec (exists_leastProperIndex D.Simple)
  have hell5 : 5 ≤ ell := nonabelianSimple_leastProperIndex_five_le
    (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) hell.1
  obtain ⟨horder,houter⟩ := hindex D.Simple D.noncommutative ell hell
  have hdegree : ell ^ D.factorCount ≤ Nat.card X :=
    primitiveSocle_power_le_degree hell5 horder (D.degreeForm hell)
  by_cases hk : D.factorCount = 1
  · have hwreath : Nat.card (Wreath (Outer D.Simple) D.factorCount) =
        Nat.card (Outer D.Simple) := by
      rw [hk]
      exact wreath_one_card (Outer D.Simple)
    have hcard : Nat.card (G ⧸ finiteGroupSocle G) ≤ Nat.card (Outer D.Simple) :=
      (Nat.card_le_card_of_injective D.quotientEmbedding
        D.quotientEmbedding_injective).trans_eq hwreath
    let e : Fin (Nat.card (G ⧸ finiteGroupSocle G)) ≃
        Fin (D.factorCount * Nat.card (G ⧸ finiteGroupSocle G)) :=
      Equiv.cast (by rw [hk,one_mul])
    have hcardR : (Nat.card (G ⧸ finiteGroupSocle G) : ℝ) ≤
        Nat.card (Outer D.Simple) := by exact_mod_cast hcard
    refine
      { profile :=
          { E := finiteGroupSocle G
            chart := D.chart
            factorCount := D.factorCount
            factorCount_pos := D.factorCount_pos
            leastIndex := ell
            leastIndex_five_le := hell5
            outerOrder := Nat.card (G ⧸ finiteGroupSocle G)
            outerOrder_pos := Nat.card_pos
            quotientAction := ?_
            quotientAction_injective := ?_
            primitive_index_lower := hdegree
            outerOrder_log_bound := hcardR.trans houter }
        factorCount_eq_chart := D.chart_card.symm
        oneFactor_socle_nontrivial := D.oneFactor_socle_nontrivial
        oneFactor_socle_le := D.oneFactor_socle_le
        oneFactor_quotientOrder := fun _ => rfl }
    · exact e.permCongrHom.toMonoidHom.comp
        (regularAction (G ⧸ finiteGroupSocle G))
    · exact e.permCongrHom.injective.comp
        (regularAction_injective (G ⧸ finiteGroupSocle G))
  · refine
      { profile :=
          { E := finiteGroupSocle G
            chart := D.chart
            factorCount := D.factorCount
            factorCount_pos := D.factorCount_pos
            leastIndex := ell
            leastIndex_five_le := hell5
            outerOrder := Nat.card (Outer D.Simple)
            outerOrder_pos := Nat.card_pos
            quotientAction := compressedAction D.quotientEmbedding
            quotientAction_injective := compressedAction_injective
              D.quotientEmbedding D.quotientEmbedding_injective D.factorCount_pos
            primitive_index_lower := hdegree
            outerOrder_log_bound := houter }
        factorCount_eq_chart := D.chart_card.symm
        oneFactor_socle_nontrivial := D.oneFactor_socle_nontrivial
        oneFactor_socle_le := D.oneFactor_socle_le
        oneFactor_quotientOrder := fun h => False.elim (hk h) }

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
