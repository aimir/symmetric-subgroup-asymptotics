import SymmetricSubgroupAsymptotics.PrimitiveAffineTwentySevenLinearEmbedding
import SymmetricSubgroupAsymptotics.PrimitiveTernaryThreeTenthsPublished
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.GroupTheory.Perm.Finite

/-! Exact degree27 complement order alternatives from the retained broader
composition catalogue. The actual affine factorization and actual faithful
linear image filter the table; no row is selected from the degree alone. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

private theorem degreeTwentySeven_order_chunk :
    ∀ r ∈ primitiveCompositionBoundRows21To27.toList,
      r.degree=27 → r.kind=.orderBound → r.groupOrder∣303264 →
      r.groupOrder=324 ∨ r.groupOrder=351 ∨ r.groupOrder=648 ∨
      r.groupOrder=702 ∨ r.groupOrder=1053 ∨ r.groupOrder=1296 ∨
      r.groupOrder=2106 ∨ r.groupOrder=151632 ∨ r.groupOrder=303264 := by
  decide +kernel

theorem primitiveCompositionBoundRow_degreeTwentySeven_order_cases
    (i : Fin 336) (hd : (primitiveCompositionBoundRow i).degree=27)
    (hk : (primitiveCompositionBoundRow i).kind=.orderBound)
    (hv : (primitiveCompositionBoundRow i).groupOrder∣303264) :
    (primitiveCompositionBoundRow i).groupOrder=324 ∨
      (primitiveCompositionBoundRow i).groupOrder=351 ∨
      (primitiveCompositionBoundRow i).groupOrder=648 ∨
      (primitiveCompositionBoundRow i).groupOrder=702 ∨
      (primitiveCompositionBoundRow i).groupOrder=1053 ∨
      (primitiveCompositionBoundRow i).groupOrder=1296 ∨
      (primitiveCompositionBoundRow i).groupOrder=2106 ∨
      (primitiveCompositionBoundRow i).groupOrder=151632 ∨
      (primitiveCompositionBoundRow i).groupOrder=303264 := by
  have hmem : primitiveCompositionBoundRow i∈primitiveCompositionBoundRows.toList := by
    unfold primitiveCompositionBoundRow
    exact Array.getElem_mem_toList _
  have hchunks :
      primitiveCompositionBoundRow i∈primitiveCompositionBoundRows2To11.toList ∨
      primitiveCompositionBoundRow i∈primitiveCompositionBoundRows12To20.toList ∨
      primitiveCompositionBoundRow i∈primitiveCompositionBoundRows21To27.toList ∨
      primitiveCompositionBoundRow i∈primitiveCompositionBoundRows28To36.toList ∨
      primitiveCompositionBoundRow i∈primitiveCompositionBoundRows37To44.toList := by
    simpa only [primitiveCompositionBoundRows,Array.toList_append,List.mem_append,or_assoc]
      using hmem
  rcases hchunks with hm | hm | hm | hm | hm
  · have h := primitiveCompositionBoundRows2To11_degree_range _ hm
    omega
  · have h := primitiveCompositionBoundRows12To20_degree_range _ hm
    omega
  · exact degreeTwentySeven_order_chunk _ hm hd hk hv
  · have h := primitiveCompositionBoundRows28To36_degree_range _ hm
    omega
  · have h := primitiveCompositionBoundRows37To44_degree_range _ hm
    omega

namespace PrimitiveAffineProfile

variable {G : Type} [Group G] [Finite G] [MulAction G (Fin 27)]
    [FaithfulSMul G (Fin 27)]

theorem complement_order_cases_degreeTwentySeven
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (P : PrimitiveAffineProfile G (Fin 27))
    (hprimitive : MulAction.IsPreprimitive G (Fin 27)) (x : Fin 27) :
    Nat.card (P.complement x)=12 ∨ Nat.card (P.complement x)=13 ∨
      Nat.card (P.complement x)=24 ∨ Nat.card (P.complement x)=26 ∨
      Nat.card (P.complement x)=39 ∨ Nat.card (P.complement x)=48 ∨
      Nat.card (P.complement x)=78 ∨ Nat.card (P.complement x)=5616 ∨
      Nat.card (P.complement x)=11232 := by
  letI := hprimitive
  have hfactor : Nat.card G=27*Nat.card (P.complement x) := by
    simpa only [P.card_eq x,Nat.card_fin] using
      (P.isComplement'_complement x).card_mul.symm
  have hdvd : Nat.card G∣303264 := by
    rw [hfactor]
    exact Nat.mul_dvd_mul_left 27
      (P.complement_card_dvd_11232_degreeTwentySeven hprimitive x)
  have hbound : Nat.card G≤303264 := Nat.le_of_dvd (by decide) hdvd
  obtain ⟨M⟩ := catalogue G (Fin 27) (by norm_num)
  cases hk : (primitiveCompositionBoundRow M.row).kind with
  | orderBound =>
      have ho := M.order_eq hk
      have hc := primitiveCompositionBoundRow_degreeTwentySeven_order_cases M.row
        (by simpa only [Nat.card_fin] using M.degree_eq) hk (ho ▸ hdvd)
      rw [←ho,hfactor] at hc
      omega
  | naturalAlternating =>
      obtain ⟨e⟩ := M.alternating_equiv hk
      have hc := Nat.card_congr e.toEquiv
      letI : Nontrivial (Fin (Nat.card (Fin 27))) :=
        Finite.one_lt_card_iff_nontrivial.mp (by simp)
      rw [nat_card_alternatingGroup] at hc
      norm_num [Nat.card_eq_fintype_card,Fintype.card_fin,Nat.factorial] at hc
      omega
  | naturalSymmetric =>
      obtain ⟨e⟩ := M.symmetric_equiv hk
      have hc := Nat.card_congr e.toEquiv
      simp only [Nat.card_fin] at hc
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin,Nat.factorial] at hc
      omega

end PrimitiveAffineProfile
end SymmetricSubgroupAsymptotics
