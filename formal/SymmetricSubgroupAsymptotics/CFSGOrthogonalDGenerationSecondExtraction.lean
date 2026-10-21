import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationShiftedTorusAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSecondEndpoint
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationScalarFilter
import SymmetricSubgroupAsymptotics.CFSGRootSubgroupExtraction

/-! Actual one-root extraction after the second endpoint. The star
torus is constructed from the two recovered lines; its inverse primitive
scalar action recovers every shifted short-root parameter, hence W and
the original short-root line. All subgroup memberships remain literal. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSecondExtraction
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDGenerationInitialElements CFSGOrthogonalDGenerationShiftedRoot
open CFSGOrthogonalDGenerationStarTorus CFSGOrthogonalDGenerationShiftedTorusAction
open CFSGOrthogonalDGenerationScalarFilter CFSGOrthogonalDGenerationPrimitiveRootSaturation
variable (K : Type) [Field K] [Finite K]

theorem star_data_extract_short (s : ℕ) (hcard : 3 ≤ Nat.card K)
    (g : Kˣ) (hg : ∀ u : Kˣ, u ∈ Subgroup.zpowers g)
    (H : Subgroup (Mat K (s + 4))ˣ)
    (hpos : ∀ a, (initialStarRoot K s false a).val ∈ H)
    (hneg : ∀ a, (initialStarRoot K s true a).val ∈ H)
    (hWA : (coxeterWeyl K (s + 3)).val * (initialShortRoot K s 1).val ∈ H) :
    (∀ a, (initialShortRoot K s a).val ∈ H) ∧ (coxeterWeyl K (s + 3)).val ∈ H := by
  let R : K → (Mat K (s + 4))ˣ := fun a => (shiftedShortRoot K s a).val
  have hAdd : ∀ a b, R (a + b) = R a * R b := fun a b =>
    congrArg Subtype.val (shiftedShortRoot_add K s a b)
  have hZero : R 0 = 1 := congrArg Subtype.val (shiftedShortRoot_zero K s)
  have hScale : ∀ a, (starTorus K s g).val * R a * (starTorus K s g).val⁻¹ =
      R ((g : K)⁻¹ * a) := fun a =>
    congrArg Subtype.val (starTorus_shifted_conjugation K s g a)
  have hScale' : ∀ a,
      ((coxeterWeyl K (s + 3)).val * (starTorus K s g).val * (coxeterWeyl K (s + 3)).val⁻¹) *
        R a *
          ((coxeterWeyl K (s + 3)).val * (starTorus K s g).val * (coxeterWeyl K (s + 3)).val⁻¹)⁻¹ =
        R ((g : K) * a) := fun a =>
    congrArg Subtype.val (conjugatedStarTorus_shifted_conjugation K s g a)
  have hComm : Commute
      ((coxeterWeyl K (s + 3)).val * (starTorus K s g).val * (coxeterWeyl K (s + 3)).val⁻¹)
      (starTorus K s g).val :=
    congrArg Subtype.val (conjugatedStarTorus_commutes K s g).eq
  have hT := starTorus_mem K s g H hpos hneg
  have hy : R 1 * (coxeterWeyl K (s + 3)).val ∈ H := by
    have he : R 1 * (coxeterWeyl K (s + 3)).val =
        (coxeterWeyl K (s + 3)).val * (initialShortRoot K s 1).val := by
      change ((coxeterWeyl K (s + 3)).val * (initialShortRoot K s 1).val *
        (coxeterWeyl K (s + 3)).val⁻¹) * (coxeterWeyl K (s + 3)).val = _
      group
    rw [he]
    exact hWA
  have hgInv : ∀ u : Kˣ, u ∈ Subgroup.zpowers g⁻¹ := by
    intro u
    simpa only [Subgroup.zpowers_inv] using hg u
  have hgi : (g : K)⁻¹ ≠ 1 := by
    simpa only [Units.val_inv_eq_inv_val] using primitive_ne_one hcard g⁻¹ hgInv
  have hm : (1 - (g : K)) * (1 - (g : K)⁻¹) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr (Ne.symm (primitive_ne_one hcard g hg)))
      (sub_ne_zero.mpr (Ne.symm hgi))
  have hM := CFSGRootSubgroupExtraction.root_mem_of_twisted_torus R hAdd hZero
    (starTorus K s g).val (coxeterWeyl K (s + 3)).val (g : K)⁻¹ (g : K)
    hScale hScale' hComm H hT hy
  have hR := all_parameters_of_primitive_scaling R hZero hAdd H (starTorus K s g).val hT
    g⁻¹ hgInv (by simpa only [Units.val_inv_eq_inv_val] using hScale) _ hm hM
  have hW : (coxeterWeyl K (s + 3)).val ∈ H := by
    have hh := H.mul_mem (H.inv_mem (hR 1)) hy
    simpa only [inv_mul_cancel_left] using hh
  refine ⟨?_, hW⟩
  intro a
  have hh := H.mul_mem (H.mul_mem (H.inv_mem hW) (hR a)) hW
  have he : (coxeterWeyl K (s + 3)).val⁻¹ * R a * (coxeterWeyl K (s + 3)).val =
      (initialShortRoot K s a).val := by
    change (coxeterWeyl K (s + 3)).val⁻¹ *
      ((coxeterWeyl K (s + 3)).val * (initialShortRoot K s a).val * (coxeterWeyl K (s + 3)).val⁻¹) *
        (coxeterWeyl K (s + 3)).val = _
    group
  rwa [he] at hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSecondExtraction
