import SymmetricSubgroupAsymptotics.CFSGTrialityGeckLongShortOrthogonality
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionHeightMembership
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootPairCommute

/-! Literal positive short sections centralize the indicated signed long
root line. The assertion uses the integer-root commutation theorem and
therefore retains characteristic two and three. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortSectionCentralizer
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckLongShortOrthogonality
open CFSGTrialityGeckSectionHeightMembership CFSGTrialityGeckFixedRootSections
open CFSGTrialityGeckFixedRootWords CFSGTrialityD4InvariantRoots
open CFSGNormTwoCoordinateRootElementRange CFSGNormTwoCoordinateRootPairCommute

local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) :=
  Classical.decEq _

private theorem root_elements_commute (K : Type) [Field K]
    (neg : Bool) (s k : Fin 3) (a b : (Matrix GeckIndex GeckIndex K)ˣ)
    (ha : a ∈ RootLine K (CFSGTrialityGeckSectionRootLabels.shortLabel (centralizerShort s) k))
    (hb : b ∈ RootLine K (signedLongRoot neg s)) : Commute a b := by
  obtain ⟨x,rfl⟩ := (mem_rootSubgroup_iff_selected (CartanMatrix.D 4)
    (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4) D4_positive_definite
    (CartanMatrix.D_off_diag_nonpos 4) K _ a).mp ha
  obtain ⟨y,rfl⟩ := (mem_rootSubgroup_iff_selected (CartanMatrix.D 4)
    (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4) D4_positive_definite
    (CartanMatrix.D_off_diag_nonpos 4) K _ b).mp hb
  exact pair_commute (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite
    (CartanMatrix.D_off_diag_nonpos 4) K _ _
    (Or.inl (short_signed_long_pairing neg s k)) x y

theorem shortFactor_commute (K : Type) [Field K] (neg : Bool) (s k : Fin 3)
    (t : K) (b : (Matrix GeckIndex GeckIndex K)ˣ)
    (hb : b ∈ RootLine K (signedLongRoot neg s)) :
    Commute (shortFactor K (centralizerShort s) k t) b :=
  root_elements_commute K neg s k _ b
    (shortFactor_mem_root K (centralizerShort s) k t) hb

theorem shortSection_commute (K : Type) [Field K] (sigma : K ≃+* K)
    (neg : Bool) (s : Fin 3) (t : K) (b : (Matrix GeckIndex GeckIndex K)ˣ)
    (hb : b ∈ RootLine K (signedLongRoot neg s)) :
    Commute (shortSection K sigma (centralizerShort s) false t) b := by
  have he : shortSection K sigma (centralizerShort s) false t =
      shortFactor K (centralizerShort s) 0 t *
      shortFactor K (centralizerShort s) 1 (sigma t) *
      shortFactor K (centralizerShort s) 2 (sigma (sigma t)) := by
    dsimp only [shortSection,shortOrbit,shortFactor]
    group <;> rfl
  rw [he]
  exact ((shortFactor_commute K neg s 0 t b hb).mul_left
    (shortFactor_commute K neg s 1 (sigma t) b hb)).mul_left
      (shortFactor_commute K neg s 2 (sigma (sigma t)) b hb)

theorem shortSection_mem_centralizer (K : Type) [Field K] (sigma : K ≃+* K)
    (neg : Bool) (s : Fin 3) (t : K) :
    shortSection K sigma (centralizerShort s) false t ∈
      Subgroup.centralizer {b : (Matrix GeckIndex GeckIndex K)ˣ | b ∈ RootLine K (signedLongRoot neg s)} := by
  intro b hb
  exact (shortSection_commute K sigma neg s t b hb).eq.symm

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortSectionCentralizer
