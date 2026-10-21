import SymmetricSubgroupAsymptotics.CFSGSymplecticElementaryCenter
import SymmetricSubgroupAsymptotics.CFSGSymplecticRootIntertwining
import SymmetricSubgroupAsymptotics.CFSGInvariantSubmoduleAction
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The literal elementary root group acts on the SAME actual integral
Serre image. Its actual action kernel equals its actual centre, giving
the first-isomorphism realization of its projective quotient. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSG.Models.Chevalley CFSGInvariantQuotientAction CFSGInvariantSubmoduleAction

theorem rootTransvection_inv (K : Type*) [CommRing K] (r : ℕ)
    (neg : Bool) (i : Fin r) (t : K) :
    (rootTransvection K r neg i t)⁻¹ = rootTransvection K r neg i (-t) := by
  apply Units.ext
  simp only [rootTransvection_inv_val, rootTransvection_val, neg_smul, sub_eq_add_neg]

theorem rootTransvection_preserves_image (K : Type) [Field K] (r : ℕ)
    (neg : Bool) (i : Fin r) (t : K) (y : Mat K r)
    (hy : y ∈ (symplecticBaseChange K r).range) :
    CFSGAlgebraConjugationAction.action K (Mat K r) (rootTransvection K r neg i t) y ∈
      (symplecticBaseChange K r).range := by
  obtain ⟨x, rfl⟩ := hy
  exact ⟨rootOperator (CartanMatrix.C r).transpose K neg i t x,
    symplecticBaseChange_rootOperator K r neg i t x⟩

theorem elementaryRootGroup_le_imageStabilizer (K : Type) [Field K] (r : ℕ) :
    elementaryRootGroup K r ≤
      (stabilizer (symplecticBaseChange K r).range).comap
        (CFSGAlgebraConjugationAction.action K (Mat K r)) := by
  apply (Subgroup.closure_le _).mpr
  rintro u ⟨neg, i, t, rfl⟩
  constructor
  · exact rootTransvection_preserves_image K r neg i t
  · intro y hy
    have hh : CFSGAlgebraConjugationAction.action K (Mat K r)
        ((rootTransvection K r neg i t)⁻¹) y ∈ (symplecticBaseChange K r).range := by
      rw [rootTransvection_inv]
      exact rootTransvection_preserves_image K r neg i (-t) y hy
    simpa only [map_inv] using hh

def elementaryToImageStabilizer (K : Type) [Field K] (r : ℕ) :
    elementaryRootGroup K r →* stabilizer (symplecticBaseChange K r).range where
  toFun u := ⟨CFSGAlgebraConjugationAction.action K (Mat K r) u.val,
    elementaryRootGroup_le_imageStabilizer K r u.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u v := Subtype.ext (map_mul _ u.val v.val)

def elementaryImageAction (K : Type) [Field K] (r : ℕ) :
    elementaryRootGroup K r →*
      ((symplecticBaseChange K r).range ≃ₗ[K] (symplecticBaseChange K r).range) :=
  (restrictionAction (symplecticBaseChange K r).range).comp (elementaryToImageStabilizer K r)

@[simp] theorem elementaryImageAction_apply (K : Type) [Field K] (r : ℕ)
    (u : elementaryRootGroup K r) (y : (symplecticBaseChange K r).range) :
    (elementaryImageAction K r u y).val =
      (u.val : Mat K r) * y.val * (↑(u.val⁻¹) : Mat K r) := rfl

theorem elementaryImageAction_ker (K : Type) [Field K] (r : ℕ) :
    (elementaryImageAction K (r + 1)).ker =
      Subgroup.center (elementaryRootGroup K (r + 1)) := by
  ext u
  change elementaryImageAction K (r + 1) u = 1 ↔
    u ∈ Subgroup.center (elementaryRootGroup K (r + 1))
  constructor
  · intro h
    apply (elementaryRootGroup_image_conjugation_kernel K r u).mp
    intro x
    have hh := DFunLike.congr_fun h ((symplecticBaseChange K (r + 1)).rangeRestrict x)
    exact congrArg Subtype.val hh
  · intro h
    have hh := (elementaryRootGroup_image_conjugation_kernel K r u).mpr h
    apply LinearEquiv.ext
    intro y
    apply Subtype.ext
    obtain ⟨x, hx⟩ := y.property
    change (u.val : Mat K (r + 1)) * y.val * (↑(u.val⁻¹) : Mat K (r + 1)) = y.val
    rw [← hx]
    exact hh x

def elementaryProjectiveActionEquiv (K : Type) [Field K] (r : ℕ) :
    (elementaryRootGroup K (r + 1) ⧸ Subgroup.center (elementaryRootGroup K (r + 1))) ≃*
      (elementaryImageAction K (r + 1)).range :=
  (QuotientGroup.quotientMulEquivOfEq (elementaryImageAction_ker K r).symm).trans
    (QuotientGroup.quotientKerEquivRange (elementaryImageAction K (r + 1)))

@[simp] theorem elementaryProjectiveActionEquiv_mk (K : Type) [Field K] (r : ℕ)
    (u : elementaryRootGroup K (r + 1)) :
    (elementaryProjectiveActionEquiv K r
      ((QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1)))) u)).val =
      elementaryImageAction K (r + 1) u := rfl

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
