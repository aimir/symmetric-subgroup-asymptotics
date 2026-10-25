import SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySylowExtensions
import SymmetricSubgroupAsymptotics.CFSGReeFFourPenultimateWordOuterInvolution
import SymmetricSubgroupAsymptotics.CFSGReeFFourReducedPositiveIntersection
import SymmetricSubgroupAsymptotics.SubgroupActionIntersectionTransport

/-! Every non-opposite retained binary relative position has a nontrivial
intersection INSIDE the SAME derived group. The checked cardinality table
handles positions 0..13; position 14 retains the WHOLE actual outer involution.
No individual E6 root is declared fixed, and no automorphism is extended. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryRelativeIntersection
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedAmbientHom
open CFSGReeFFourDerivedAmbientHom CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFieldParameters CFSGReeFFourOuterFixedRoot
open CFSGReeFFourOuterFixedInversion CFSGReeFFourOuterThreeWord
open CFSGReeFFourBinaryOuterSaving CFSGReeFFourBinarySylowExtensions
open CFSGReeFFourPenultimateWordOuterInvolution CFSGReeFFourReducedPositiveIntersection
open CFSGReeFFourFixedPositiveCardinality CFSGReeFFourShortPairedWeylMenu
open FiniteNormalSylowPairExtension
private instance fixedFinite : Finite (originalModelFixed 0) :=
  Finite.of_injective (fixedAmbientHom 0) (fixedAmbientHom_injective 0)

def shortDerivedIntersection (m : ℕ) (i : Fin 16) :
    Subgroup (commutator (originalModelFixed m)) :=
  (shortPositiveIntersection m i).comap (commutator (originalModelFixed m)).subtype

theorem outer_mem_positive (m : ℕ) : outerInvolution m ∈ fixedPositive m := by
  have h : outerInvolution m ∈ fixedOuterInversion m := by
    rw [fixedOuterInversion_eq_range]
    exact ⟨Multiplicative.ofAdd (1 : Field m), rfl⟩
  exact h.1

theorem outer_ne_one (m : ℕ) : outerInvolution m ≠ 1 := by
  intro h
  have hh : fixedOuterHom m (Multiplicative.ofAdd (1 : Field m)) = fixedOuterHom m 1 :=
    h.trans (map_one (fixedOuterHom m)).symm
  have he := fixedOuterHom_injective m hh
  exact one_ne_zero (congrArg (fun a : Multiplicative (Field m) => a.toAdd) he)

theorem outer_mem_penultimate_intersection (m : ℕ) :
    outerInvolution m ∈ shortPositiveIntersection m (14 : Fin 16) := by
  exact SubgroupActionIntersectionTransport.mem_intersection_of_map_eq
    (fixedPositive m) (MulAut.conj (shortModelWord m (14 : Fin 16))).toMonoidHom
    (outerInvolution m) (outer_mem_positive m) (penultimate_conjugates_outer m)

private theorem small_weight : ∀ i : Fin 16, i.val ≤ 13 → inversionWeight i ≤ 10 := by
  decide +kernel

theorem short_intersection_card_ge_four (i : Fin 16) (hi : i.val ≤ 13) :
    4 ≤ Nat.card (shortPositiveIntersection 0 i) := by
  have h := shortPositiveIntersection_card_factorization 0 i
  rw [fixedPositive_card] at h
  have hc : (4096 : ℕ) = Nat.card (shortPositiveIntersection 0 i) * 2^(inversionWeight i) := h
  have hp : 2^(inversionWeight i) ≤ 1024 :=
    Nat.pow_le_pow_right (by decide) (small_weight i hi)
  by_contra hn
  have hs : Nat.card (shortPositiveIntersection 0 i) ≤ 3 := by omega
  have hm := Nat.mul_le_mul hs hp
  rw [← hc] at hm
  omega

theorem non_opposite_derived_intersection_ne_bot (i : Fin 16) (hi : i ≠ (15 : Fin 16)) :
    shortDerivedIntersection 0 i ≠ ⊥ := by
  intro he
  by_cases hs : i.val ≤ 13
  · have hc : Nat.card (shortPositiveIntersection 0 i) ≤ 2 :=
      (card_le_index_of_comap_eq_bot (commutator (originalModelFixed 0))
        (shortPositiveIntersection 0 i) he).trans derived_index_le_two
    have hfour := short_intersection_card_ge_four i hs
    omega
  · have hne : i.val ≠ 15 := fun h => hi (Fin.ext h)
    have hei : i = (14 : Fin 16) := Fin.ext (by omega)
    subst i
    let x : commutator (originalModelFixed 0) := ⟨outerInvolution 0, outer_mem_derived 0⟩
    have hx : x ∈ shortDerivedIntersection 0 (14 : Fin 16) :=
      outer_mem_penultimate_intersection 0
    rw [he, Subgroup.mem_bot] at hx
    have hxe : outerInvolution 0 = 1 :=
      congrArg (fun z : commutator (originalModelFixed 0) => z.val) hx
    exact outer_ne_one 0 hxe

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryRelativeIntersection
