import SymmetricSubgroupAsymptotics.SixPointAlternatingSymmetricGenerators
import SymmetricSubgroupAsymptotics.AlternatingSymmetricNormalChain
import SymmetricSubgroupAsymptotics.AffineIrreducibleConjugation

/-! Exact six-point deleted-module sources for the original row16/17
linear complements. The basis changes are displayed four-bit maps. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRows16And17Complements

open BinarySixDeletedRepresentation
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

/-- Columns are masks [2,7,9,8] in the unchanged original labels. -/
def chart16 : LinearGroup where
  toFun v := ![v 1 + v 2, v 0 + v 1, v 1, v 2 + v 3]
  invFun v := ![v 1 + v 2, v 2, v 0 + v 2, v 0 + v 2 + v 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

/-- Columns are masks [2,3,9,14]. -/
def chart17 : LinearGroup where
  toFun v := ![v 1 + v 2, v 0 + v 1 + v 3, v 3, v 2 + v 3]
  invFun v := ![v 0 + v 1 + v 3, v 0 + v 2 + v 3, v 2 + v 3, v 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

abbrev hom16 := conjugateHom chart16
abbrev hom17 := conjugateHom chart17

theorem hom16_alpha_original :
    BinaryFourAffineImage.linearPerm (hom16 alpha) =
      DegreeTwoPrimitiveSixteenInterfaces.row16Generators 0 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem hom16_beta_original :
    BinaryFourAffineImage.linearPerm (hom16 beta16) =
      DegreeTwoPrimitiveSixteenInterfaces.row16Generators 1 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem hom17_alpha_original :
    BinaryFourAffineImage.linearPerm (hom17 alpha) =
      DegreeTwoPrimitiveSixteenInterfaces.row17Generators 0 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem hom17_beta_original :
    BinaryFourAffineImage.linearPerm (hom17 beta17) =
      DegreeTwoPrimitiveSixteenInterfaces.row17Generators 1 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

abbrev R16 : Subgroup LinearGroup := Subgroup.closure ({hom16 alpha, hom16 beta16} : Set LinearGroup)
abbrev R17 : Subgroup LinearGroup := Subgroup.closure ({hom17 alpha, hom17 beta17} : Set LinearGroup)

theorem alpha_mem16 : hom16 alpha ∈ R16 := Subgroup.subset_closure (by simp)
theorem beta_mem16 : hom16 beta16 ∈ R16 := Subgroup.subset_closure (by simp)
theorem alpha_mem17 : hom17 alpha ∈ R17 := Subgroup.subset_closure (by simp)
theorem beta_mem17 : hom17 beta17 ∈ R17 := Subgroup.subset_closure (by simp)

def evenHom17 : alternatingGroup (Fin 6) →* LinearGroup :=
  hom17.comp (alternatingGroup (Fin 6)).subtype

theorem hom16_range : hom16.range = R16 := by
  rw [MonoidHom.range_eq_map, ← SixPointAlternatingSymmetricGenerators.symmetric_generators,
    MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton]

theorem evenHom17_range : evenHom17.range = R17 := by
  change (hom17.comp (alternatingGroup (Fin 6)).subtype).range = R17
  rw [MonoidHom.range_comp, Subgroup.range_subtype,
    ← SixPointAlternatingSymmetricGenerators.alternating_generators, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton]

def complementMap16 : Equiv.Perm (Fin 6) →* R16 :=
  (MulEquiv.subgroupCongr hom16_range).toMonoidHom.comp hom16.rangeRestrict

def complementMap17 : alternatingGroup (Fin 6) →* R17 :=
  (MulEquiv.subgroupCongr evenHom17_range).toMonoidHom.comp evenHom17.rangeRestrict

theorem complementMap16_surjective : Function.Surjective complementMap16 :=
  (MulEquiv.subgroupCongr hom16_range).surjective.comp hom16.rangeRestrict_surjective

theorem complementMap17_surjective : Function.Surjective complementMap17 :=
  (MulEquiv.subgroupCongr evenHom17_range).surjective.comp evenHom17.rangeRestrict_surjective

theorem linear_normal_total16 (A B : Subgroup R16) (hA : A.Normal) (hB : B.Normal) :
    A ≤ B ∨ B ≤ A :=
  normalSubgroups_total_of_surjective (G := Equiv.Perm (Fin 6)) (H := R16)
    complementMap16 complementMap16_surjective
    (AlternatingSymmetricNormalChain.symmetric_normal_total (X := Fin 6) (by norm_num)) A B hA hB

theorem linear_normal_total17 (A B : Subgroup R17) (hA : A.Normal) (hB : B.Normal) :
    A ≤ B ∨ B ≤ A :=
  normalSubgroups_total_of_surjective (G := alternatingGroup (Fin 6)) (H := R17)
    complementMap17 complementMap17_surjective
    (AlternatingSymmetricNormalChain.alternating_normal_total (X := Fin 6) (by norm_num)) A B hA hB

/-- Any second generator may be added: the displayed five-cycle already
acts irreducibly after the given basis change. -/
theorem irreducible_pair (e : LinearGroup) (β : Equiv.Perm (Fin 6)) :
    AffineModel.Irreducible
      (Subgroup.closure ({conjugateHom e alpha, conjugateHom e β} : Set LinearGroup)) := by
  let S := Subgroup.closure ({conjugateHom e alpha, conjugateHom e β} : Set LinearGroup)
  apply AffineModel.irreducible_of_conjugate_le
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.linearGroup S e
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.irreducible
  apply Subgroup.map_le_iff_le_comap.mpr
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  fin_cases i
  change (MulAut.conj e) PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.cycle ∈ S
  have ha : conjugateHom e alpha ∈ S := Subgroup.subset_closure (by simp)
  have hi := S.inv_mem ha
  simpa only [conjugateHom, MonoidHom.comp_apply, hom_alpha, map_inv, inv_inv] using hi

theorem irreducible16 : AffineModel.Irreducible R16 := irreducible_pair chart16 beta16
theorem irreducible17 : AffineModel.Irreducible R17 := irreducible_pair chart17 beta17

end PrimitiveAffineDegreeTwoPrimitiveSixteenRows16And17Complements
end SymmetricSubgroupAsymptotics

end
