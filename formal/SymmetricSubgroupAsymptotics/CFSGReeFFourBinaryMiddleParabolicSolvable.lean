import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryAssociatedImage
import Mathlib.GroupTheory.Nilpotent

/-! Solubility descends through the EXACT graded two-kernel of the actual
binary middle parabolic. The literal derived intersection and its image
through the FULL derived-centre quotient are retained. No Sylow-normalizer
identification, derived-index-two assertion, or global capacity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryMiddleParabolicSolvable
open CFSGReeFFourBinaryAssociatedImage CFSGReeFFourMiddleAssociatedQuotient
open CFSGReeFFourMiddleGradedKernel CFSGReeFFourMiddleGradedDerivedAction
open CFSGReeFFourMiddleParabolicFlag CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedAmbientHom CFSGReeFFourOriginalPositiveSylow
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance fixedFinite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

private theorem solvable_of_kernel_and_range {G H : Type*} [Group G] [Group H]
    (rho : G →* H) (N : Subgroup G) (hker : rho.ker=N)
    [IsSolvable N] [IsSolvable rho.range] : IsSolvable G :=
  solvable_of_ker_le_range N.subtype rho.rangeRestrict (by
    rw [MonoidHom.ker_rangeRestrict,hker,Subgroup.range_subtype])

private theorem map_solvable {G H : Type*} [Group G] [Group H]
    (rho : G →* H) (N : Subgroup G) [IsSolvable N] : IsSolvable (N.map rho) := by
  let F : N →* N.map rho :=
    (rho.comp N.subtype).codRestrict _ (fun n => ⟨n.val,n.property,rfl⟩)
  have hF : Function.Surjective F := by
    intro x
    obtain ⟨n,hn,he⟩ := x.property
    exact ⟨⟨n,hn⟩,Subtype.ext he⟩
  exact solvable_of_surjective (f := F) hF

theorem gradedKernel_solvable (m : ℕ) : IsSolvable (gradedKernel m) := by
  letI : Group.IsNilpotent (gradedKernel m) := (gradedKernel_isPGroup m).isNilpotent
  infer_instance

theorem middleParabolic_zero_solvable : IsSolvable (middleParabolic 0) := by
  letI : IsSolvable (gradedKernel 0) := gradedKernel_solvable 0
  letI : IsSolvable (middleAssociatedHom 0).range := image_solvable
  exact solvable_of_kernel_and_range (middleAssociatedHom 0) (gradedKernel 0)
    (middleAssociatedHom_ker 0)

theorem derivedParabolic_zero_solvable : IsSolvable (derivedParabolic 0) := by
  letI : IsSolvable (middleParabolic 0) := middleParabolic_zero_solvable
  exact solvable_of_solvable_injective (f := toParabolic 0) (toParabolic_injective 0)

def originalParabolic (m : ℕ) : Subgroup (CFSG.Models.ReeF4 m) :=
  (derivedParabolic m).map (derivedReeHom m)

theorem originalParabolic_zero_solvable : IsSolvable (originalParabolic 0) := by
  letI : IsSolvable (derivedParabolic 0) := derivedParabolic_zero_solvable
  exact map_solvable (derivedReeHom 0) (derivedParabolic 0)

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryMiddleParabolicSolvable
