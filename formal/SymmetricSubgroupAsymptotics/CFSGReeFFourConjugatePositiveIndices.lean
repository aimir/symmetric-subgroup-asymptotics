import SymmetricSubgroupAsymptotics.CFSGReeFFourReducedPositiveIntersection
import SymmetricSubgroupAsymptotics.CFSGReeFFourBorelIntersection
import SymmetricSubgroupAsymptotics.SubgroupActionIntersectionTransport
import Mathlib.GroupTheory.Index

/-! Actual relative indices of intersections of the full fixed-positive
subgroup with its conjugates. The original short-cell cover reduces each
intersection cardinality to the already proved exact short intersection.
The same Borel coordinates give the exact normalizer/Sylow relative index. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourConjugatePositiveIndices
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedAmbientHom
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourShortPairedWeylMenu
open CFSGReeFFourReducedPositiveIntersection CFSGReeFFourFixedBorelCardinality
open CFSGReeFFourBorelIntersection CFSGReeFFourFixedPositiveCardinality
open SubgroupActionIntersectionTransport

private instance fixedFinite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

private theorem card_mul_relIndex {G : Type*} [Group G] [Finite G]
    (R U : Subgroup G) (h : R≤U) : Nat.card R*R.relIndex U=Nat.card U := by
  have hh := (R.subgroupOf U).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv] at hh
  exact hh

private theorem card_comap_aut {G : Type*} [Group G] (R : Subgroup G) (f : MulAut G) :
    Nat.card (R.comap f.toMonoidHom)=Nat.card R := by
  rw [Subgroup.comap_equiv_eq_map_symm']
  exact Subgroup.card_map_of_injective f.symm.injective

def positiveIntersection (m : ℕ) (g : originalModelFixed m) : Subgroup (originalModelFixed m) :=
  fixedPositive m ⊓ (fixedPositive m).map (MulAut.conj g).toMonoidHom

theorem exists_short_intersection_index (m : ℕ) (g : originalModelFixed m) :
    ∃ i : Fin 16, (positiveIntersection m g).relIndex (fixedPositive m) =
      (2^(2*m+1))^(inversionWeight i) := by
  obtain ⟨u,d,i,v,he⟩ := exists_short_fixed_cell m g⁻¹
  have hn : u.val*d.val∈Subgroup.normalizer (fixedPositive m : Set (originalModelFixed m)) :=
    fixedBorel_le_normalizer m ((fixedBorel m).mul_mem
      (positive_le_borel m u.property) (diagonal_le_borel m d.property))
  have hu : ∀ x : originalModelFixed m,
      MulAut.conj (u.val*d.val) x∈fixedPositive m ↔ x∈fixedPositive m :=
    fun x => (Subgroup.mem_normalizer_iff.mp hn x).symm
  have hv : ∀ x : originalModelFixed m,
      MulAut.conj v.val x∈fixedPositive m ↔ x∈fixedPositive m :=
    fun x => (Subgroup.mem_normalizer_iff.mp ((fixedPositive m).le_normalizer v.property) x).symm
  have htransport : fixedPositive m ⊓ (fixedPositive m).comap
      (MulAut.conj g⁻¹).toMonoidHom =
      (shortPositiveIntersection m i).comap (MulAut.conj v.val).toMonoidHom := by
    rw [he]
    exact comap_intersection_mul (MulAut.conj) (fixedPositive m)
      (u.val*d.val) (shortModelWord m i) v.val hu hv
  have hI : positiveIntersection m g = fixedPositive m ⊓
      (fixedPositive m).comap (MulAut.conj g⁻¹).toMonoidHom := by
    unfold positiveIntersection
    rw [map_eq_comap_inverse (MulAut.conj) (fixedPositive m) g]
  have hc : Nat.card (positiveIntersection m g)=Nat.card (shortPositiveIntersection m i) := by
    rw [hI,htransport]
    exact card_comap_aut _ _
  have hprod := card_mul_relIndex (positiveIntersection m g) (fixedPositive m) inf_le_left
  rw [hc] at hprod
  have hchart := shortPositiveIntersection_card_factorization m i
  exact ⟨i,Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α:=shortPositiveIntersection m i))
    (hprod.trans hchart)⟩

theorem field_dvd_proper_intersection_index (m : ℕ) (g : originalModelFixed m)
    (hproper : positiveIntersection m g≠fixedPositive m) :
    2^(2*m+1) ∣ (positiveIntersection m g).relIndex (fixedPositive m) := by
  obtain ⟨i,hi⟩ := exists_short_intersection_index m g
  have hw : inversionWeight i≠0 := by
    intro he
    have h1 : (positiveIntersection m g).relIndex (fixedPositive m)=1 := by
      simpa only [he,pow_zero] using hi
    have hUI : fixedPositive m≤positiveIntersection m g :=
      (Subgroup.relIndex_eq_one (H:=positiveIntersection m g) (K:=fixedPositive m)).mp h1
    exact hproper (le_antisymm inf_le_left hUI)
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hw
  rw [hi]
  exact ⟨(2^(2*m+1))^k,by rw [hk,pow_succ']⟩

theorem positive_normalizer_relIndex (m : ℕ) :
    (fixedPositive m).relIndex (Subgroup.normalizer (fixedPositive m : Set (originalModelFixed m))) =
      (2^(2*m+1)-1)^2 := by
  have hN : Nat.card (Subgroup.normalizer (fixedPositive m : Set (originalModelFixed m))) =
      Nat.card (fixedPositive m)*(2^(2*m+1)-1)^2 := by
    rw [←fixedBorel_eq_positive_normalizer,fixedBorel_card,fixedPositive_card]
  have hc := card_mul_relIndex (fixedPositive m)
    (Subgroup.normalizer (fixedPositive m : Set (originalModelFixed m))) (fixedPositive m).le_normalizer
  rw [hN] at hc
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α:=fixedPositive m)) hc

end SymmetricSubgroupAsymptotics.CFSGReeFFourConjugatePositiveIndices
