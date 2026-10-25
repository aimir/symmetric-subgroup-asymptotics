import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveAssociatedOuter
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterConstantSubgroup
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryMiddleGenerators
import Mathlib.GroupTheory.Solvable

/-! The actual binary outer associated image is contained in the raw
image of the proved soluble constant subgroup of cardinality at most six.
Containment follows from literal positive and Weyl generation of the SAME
parabolic; no rank-one model or image-generation premise is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOuterAssociatedImage
open CFSGReeFFourFixedPositiveAssociatedOuter CFSGReeFFourOuterGradedQuotient
open CFSGReeFFourOuterConstantSubgroup CFSGReeFFourOuterThreeWord
open CFSGReeFFourBinaryMiddleGenerators CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFixedAmbientHom
open CFSGReeFFourOuterParabolicFlag CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourOuterFixedRoot CFSGReeFFourFieldParameters
open CFSGReeFFourRelativeSimpleWeyl
open CFSGFFourOriginalMiddleWords CFSGReeFFourRelativeWeylRawWords
open CFSGNormTwoGeckIntegralWord CFSGNormTwoGeckNonnegativeHeightFlag
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGGradedMatrixSubgroups
open CFSGGradedMatrixAssociatedUnitHom
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
private instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _
private instance fixedFinite : Finite (originalModelFixed 0) :=
  Finite.of_injective (fixedAmbientHom 0) (fixedAmbientHom_injective 0)
private abbrev P := outerParabolic 0
private abbrev f := outerAssociatedHom 0
private abbrev R := (outerConstantSubgroup 0).map (fixedRawHom 0)

private theorem raw_injective : Function.Injective (fixedRawHom 0) := by
  intro x y h
  apply Subtype.ext
  exact rawHom_injective (Field 0) h

theorem fixedOuter_zero_range_le_constant : (fixedOuterHom 0).range ≤ outerConstantSubgroup 0 := by
  rintro x ⟨a, rfl⟩
  have ha2 : a.toAdd^2 = a.toAdd := by
    have h := field_cycle 0 a.toAdd
    norm_num at h
    exact h
  have hz : a.toAdd * (a.toAdd-1) = 0 := by
    calc
      _ = a.toAdd^2-a.toAdd := by ring
      _ = 0 := by rw [ha2, sub_self]
  rcases mul_eq_zero.mp hz with hzero | hone
  · have he : a = 1 := Multiplicative.toAdd.injective hzero
    rw [he, map_one]
    exact (outerConstantSubgroup 0).one_mem
  · have he : a = Multiplicative.ofAdd (1 : Field 0) :=
      Multiplicative.toAdd.injective (sub_eq_zero.mp hone)
    rw [he]
    exact outerInvolution_mem_constant 0

def outerWeylInParabolic : P :=
  ⟨outerFixedWeyl 0,
    (show Subgroup.closure {outerFixedWeyl 0} ≤ P from le_sup_right)
      (Subgroup.subset_closure (Set.mem_singleton _))⟩

theorem outerWeyl_associated_value : f outerWeylInParabolic = fixedRawHom 0 (outerFixedWeyl 0) := by
  apply associatedUnit_eq_of_preserving outerWeight (parabolicToTriangular 0 outerWeylInParabolic)
  change rawHom (Field 0) (outerRelativeWeyl 0) ∈ preservingUnits outerWeight
  rw [rawHom_outerRelativeWeyl, word_eq_canonicalWord]
  apply zero_degree_word_preserving A hs hp E6Base E6Index insideHeight (Field 0) [0,5,1]
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> rfl

theorem image_le_constant_raw : f.range ≤ R := by
  let S : Subgroup (originalModelFixed 0) := (R.comap f).map P.subtype
  have hU : fixedPositive 0 ≤ S := by
    intro u hu
    let U : P := ⟨u, positive_le_parabolic 0 hu⟩
    obtain ⟨a, ha⟩ := exists_outer_associated_value 0 U hu
    have hvalue : f U ∈ R := by
      change outerAssociatedHom 0 U ∈ R
      rw [ha]
      exact ⟨fixedOuterHom 0 a, fixedOuter_zero_range_le_constant ⟨a, rfl⟩, rfl⟩
    exact ⟨U, hvalue, rfl⟩
  have hW : f outerWeylInParabolic ∈ R := by
    rw [outerWeyl_associated_value]
    exact ⟨outerFixedWeyl 0, outerWeyl_mem_constant 0, rfl⟩
  have hPS : P ≤ S := by
    change (fixedPositive 0 ⊔ CFSGReeFFourFixedBruhatCover.fixedDiagonal 0) ⊔
      Subgroup.closure {outerFixedWeyl 0} ≤ S
    apply sup_le
    · apply sup_le hU
      rw [fixedDiagonal_zero_eq_bot]
      exact bot_le
    · apply (Subgroup.closure_le _).mpr
      intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact ⟨outerWeylInParabolic, hW, rfl⟩
  rintro _ ⟨p, rfl⟩
  obtain ⟨q, hq, he⟩ := hPS p.property
  have hqp : q = p := Subtype.ext he
  exact hqp ▸ hq

theorem image_card_le_six : Nat.card f.range ≤ 6 := by
  calc
    Nat.card f.range ≤ Nat.card R := Subgroup.card_le_of_le image_le_constant_raw
    _ = Nat.card (outerConstantSubgroup 0) := Subgroup.card_map_of_injective raw_injective
    _ ≤ 6 := outerConstantSubgroup_card_le_six 0

private theorem map_solvable {G H : Type*} [Group G] [Group H]
    (rho : G →* H) (N : Subgroup G) [IsSolvable N] : IsSolvable (N.map rho) := by
  let F : N →* N.map rho :=
    (rho.comp N.subtype).codRestrict _ (fun n => ⟨n.val, n.property, rfl⟩)
  have hF : Function.Surjective F := by
    intro x
    obtain ⟨n, hn, he⟩ := x.property
    exact ⟨⟨n, hn⟩, Subtype.ext he⟩
  exact solvable_of_surjective (f := F) hF

theorem image_solvable : IsSolvable f.range := by
  letI : IsSolvable (outerConstantSubgroup 0) := outerConstantSubgroup_solvable 0
  letI : IsSolvable R := map_solvable (fixedRawHom 0) (outerConstantSubgroup 0)
  exact solvable_of_solvable_injective (f := Subgroup.inclusion image_le_constant_raw)
    (Subgroup.inclusion_injective image_le_constant_raw)

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOuterAssociatedImage
