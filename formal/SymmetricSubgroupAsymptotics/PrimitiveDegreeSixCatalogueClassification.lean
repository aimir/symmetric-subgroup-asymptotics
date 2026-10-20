import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixRecognition
import SymmetricSubgroupAsymptotics.PrimitiveTernaryThreeTenthsPublished
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixChiefPublished
import Mathlib.Order.Atoms.Finite

/-! The degree-six classification follows from the already retained bounded
primitive composition catalogue. The order-60 case uses that same catalogue
only to exclude a hypothetical primitive action of S₆ on twelve cosets. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
open Equiv Subgroup MulAction
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.PrimitiveDegreeSixCatalogueClassification

open PrimitiveDegreeSixRecognition

private theorem degree_six_orders : ∀ i : Fin 336,
    (primitiveCompositionBoundRow i).degree = 6 →
    (primitiveCompositionBoundRow i).kind = .orderBound →
    (primitiveCompositionBoundRow i).groupOrder = 60 ∨
      (primitiveCompositionBoundRow i).groupOrder = 120 := by decide +kernel

private theorem degree_twelve_order_ne : ∀ i : Fin 336,
    (primitiveCompositionBoundRow i).degree = 12 →
    (primitiveCompositionBoundRow i).kind = .orderBound →
    (primitiveCompositionBoundRow i).groupOrder ≠ 720 := by decide +kernel

/-- The retained primitive catalogue excludes an order-720 degree-12 action. -/
theorem no_order720_degree12
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X]
    (hdegree : Nat.card X = 12) (horder : Nat.card G = 720) : False := by
  obtain ⟨M⟩ := catalogue G X (by omega)
  have hd : (primitiveCompositionBoundRow M.row).degree = 12 := M.degree_eq.trans hdegree
  cases hk : (primitiveCompositionBoundRow M.row).kind with
  | orderBound =>
      exact degree_twelve_order_ne M.row hd hk ((M.order_eq hk).symm.trans horder)
  | naturalAlternating =>
      obtain ⟨e⟩ := M.alternating_equiv hk
      have h := Nat.card_congr e.toEquiv
      rw [hdegree, horder] at h
      rw [nat_card_alternatingGroup] at h
      norm_num [Nat.card_eq_fintype_card,
        Fintype.card_fin, Nat.factorial] at h
  | naturalSymmetric =>
      obtain ⟨e⟩ := M.symmetric_equiv hk
      have h := Nat.card_congr e.toEquiv
      rw [hdegree, horder] at h
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_fin, Nat.factorial] at h

private theorem divides_twelve (n : ℕ) (hn : n ∣ 12) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 12 := by
  have hmem := Nat.mem_divisors.mpr ⟨hn, by decide⟩
  have hset : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} := by decide
  rw [hset] at hmem
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem

/-- Order-60 subgroups of S₆ are A₅. The catalogue dependency is explicit:
it is applied to a new maximal-overgroup coset action, not to a certificate
asserting this recognition conclusion. -/
def subgroupSixtyEquiv
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (H : Subgroup (Equiv.Perm (Fin 6))) (hH : Nat.card H = 60) :
    H ≃* alternatingGroup (Fin 5) := Classical.choice <| by
  have hn : H ≠ ⊤ := by
    intro h
    have hh := hH
    rw [h, Nat.card_congr (Subgroup.topEquiv :
      (⊤ : Subgroup (Equiv.Perm (Fin 6))) ≃* Equiv.Perm (Fin 6)).toEquiv,
      card_perm_six] at hh
    omega
  obtain ⟨K, hK, hHK⟩ := (eq_top_or_exists_le_coatom H).resolve_left hn
  have hHi : H.index = 12 := by
    have h := H.card_mul_index
    rw [hH, card_perm_six] at h
    omega
  have hKi : 1 < K.index := K.one_lt_index_of_ne_top hK.ne_top
  by_cases hc : K.normalCore = ⊥
  · have hfaith : Function.Injective
        (MulAction.toPermHom (Equiv.Perm (Fin 6)) (Equiv.Perm (Fin 6) ⧸ K)) := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [← Subgroup.normalCore_eq_ker K, hc]
    letI : FaithfulSMul (Equiv.Perm (Fin 6)) (Equiv.Perm (Fin 6) ⧸ K) :=
      ⟨fun {_ _} h => hfaith (Equiv.ext h)⟩
    have hcardQ : Nat.card (Equiv.Perm (Fin 6) ⧸ K) = K.index := K.index_eq_card.symm
    letI : Nontrivial (Equiv.Perm (Fin 6) ⧸ K) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hcardQ]; exact hKi)
    letI : MulAction.IsPreprimitive (Equiv.Perm (Fin 6)) (Equiv.Perm (Fin 6) ⧸ K) := by
      apply (MulAction.isCoatom_stabilizer_iff_preprimitive (Equiv.Perm (Fin 6))
        (((1 : Equiv.Perm (Fin 6))) : Equiv.Perm (Fin 6) ⧸ K)).mp
      rwa [MulAction.stabilizer_quotient]
    have hbound := Nat.card_le_card_of_injective _ hfaith
    rw [card_perm_six, Nat.card_eq_fintype_card, Fintype.card_perm,
      ← Nat.card_eq_fintype_card, hcardQ] at hbound
    have hdvd : K.index ∣ 12 := hHi ▸ Subgroup.index_dvd_of_le hHK
    have hidx : K.index = 6 := by
      rcases divides_twelve K.index hdvd with h | h | h | h | h | h
      · omega
      · norm_num [h, Nat.factorial] at hbound
      · norm_num [h, Nat.factorial] at hbound
      · norm_num [h, Nat.factorial] at hbound
      · exact h
      · exact (no_order720_degree12 catalogue (Equiv.Perm (Fin 6))
          (Equiv.Perm (Fin 6) ⧸ K) (hcardQ.trans h) card_perm_six).elim
    have hcardK : Nat.card K = 120 := by
      have h := K.card_mul_index
      rw [hidx, card_perm_six] at h
      omega
    have hcardHK : Nat.card (H.subgroupOf K) = 60 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv]
      exact hH
    exact ⟨(Subgroup.subgroupOfEquivOfLe hHK).symm.trans <|
      indexTwoEquiv (PGLTwoFiveRecognition.subgroupEquiv K hcardK) (H.subgroupOf K) hcardHK⟩
  · have hnt : Nontrivial K.normalCore := K.normalCore.nontrivial_iff_ne_bot.mpr hc
    have hA : alternatingGroup (Fin 6) ≤ K :=
      (Equiv.Perm.alternatingGroup_le_of_normal (by simp) hnt).trans K.normalCore_le
    have hcardK : 360 ≤ Nat.card K := by
      simpa only [card_alt_six] using Subgroup.card_le_of_le hA
    have hmul := Nat.mul_le_mul_right K.index hcardK
    rw [K.card_mul_index] at hmul
    rw [card_perm_six] at hmul
    have hidx : K.index = 2 := by omega
    have heq : K = alternatingGroup (Fin 6) :=
      Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx
    have hHA : H ≤ alternatingGroup (Fin 6) := heq ▸ hHK
    have hcardHA : Nat.card (H.subgroupOf (alternatingGroup (Fin 6))) = 60 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHA).toEquiv]
      exact hH
    exact ⟨(Subgroup.subgroupOfEquivOfLe hHA).symm.trans <|
      alternatingSubgroupEquiv (H.subgroupOf (alternatingGroup (Fin 6))) hcardHA⟩

/-- The four exact degree-six isomorphism types follow from the retained
composition catalogue, so this slice needs no independent literature premise. -/
theorem publishedPrimitiveDegreeSixClassification_of_compositionCatalogue
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence) :
    PublishedPrimitiveDegreeSixClassification := by
  intro G X _ _ _ _ _ _ _ hdegree
  obtain ⟨M⟩ := catalogue G X (by omega)
  have hd : (primitiveCompositionBoundRow M.row).degree = 6 := M.degree_eq.trans hdegree
  cases hk : (primitiveCompositionBoundRow M.row).kind with
  | orderBound =>
      let e : X ≃ Fin 6 :=
        Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card]; exact hdegree)
      let P := labelledActionImage (A := G) e
      let E : G ≃* P := faithfulLabelledActionEquiv e
      rcases degree_six_orders M.row hd hk with h60 | h120
      · have hP : Nat.card P = 60 :=
          (Nat.card_congr E.toEquiv).symm.trans ((M.order_eq hk).trans h60)
        exact Or.inl ⟨E.trans (subgroupSixtyEquiv catalogue P hP)⟩
      · have hP : Nat.card P = 120 :=
          (Nat.card_congr E.toEquiv).symm.trans ((M.order_eq hk).trans h120)
        exact Or.inr (Or.inl ⟨E.trans (PGLTwoFiveRecognition.subgroupEquiv P hP)⟩)
  | naturalAlternating =>
      exact Or.inr (Or.inr (Or.inl (hdegree ▸ M.alternating_equiv hk)))
  | naturalSymmetric =>
      exact Or.inr (Or.inr (Or.inr (hdegree ▸ M.symmetric_equiv hk)))

end SymmetricSubgroupAsymptotics.PrimitiveDegreeSixCatalogueClassification
