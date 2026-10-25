import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOuterAssociatedImage
import Mathlib.GroupTheory.Nilpotent

/-! Solubility of the literal binary outer parabolic follows through its
exact graded two-kernel and its actual soluble associated image. No
normalizer, derived-index or two-Sylow generation assertion is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOuterParabolicSolvable
open CFSGReeFFourBinaryOuterAssociatedImage CFSGReeFFourOuterGradedQuotient
open CFSGReeFFourOuterParabolicFlag CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedAmbientHom
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance fixedFinite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

private theorem solvable_of_kernel_and_range {G H : Type*} [Group G] [Group H]
    (rho : G →* H) (N : Subgroup G) (hker : rho.ker=N)
    [IsSolvable N] [IsSolvable rho.range] : IsSolvable G :=
  solvable_of_ker_le_range N.subtype rho.rangeRestrict (by
    rw [MonoidHom.ker_rangeRestrict, hker, Subgroup.range_subtype])

theorem gradedKernel_solvable (m : ℕ) : IsSolvable (gradedKernel m) := by
  letI : Group.IsNilpotent (gradedKernel m) := (gradedKernel_isPGroup m).isNilpotent
  infer_instance

theorem outerParabolic_zero_solvable : IsSolvable (outerParabolic 0) := by
  letI : IsSolvable (gradedKernel 0) := gradedKernel_solvable 0
  letI : IsSolvable (outerAssociatedHom 0).range := image_solvable
  exact solvable_of_kernel_and_range (outerAssociatedHom 0) (gradedKernel 0)
    (outerAssociatedHom_ker 0)

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOuterParabolicSolvable
