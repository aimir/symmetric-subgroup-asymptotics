import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryCharts
import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightNaturalHeads
import SymmetricSubgroupAsymptotics.InvariantKernelQuotientRepresentatives

/-! One selected three-coordinate quotient pilot. Five kernel columns,
eight quotient-defect columns and eight factorization columns prove the
needed difference-kernel inclusion. No group/cocycle/lift census occurs. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergFourteenQuotientKernelInclusion
local instance heisenbergFourteenQuotientKernelPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
abbrev V := Fin 8 → ZMod 2
abbrev S := BinaryRegularEightNaturalRegistry.chart33
def projection : V →ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
  (binaryRectangularMatrixOfColumnMasks 3 8 (![1,2,2,4,4,7,7,1] : Fin 8 → ℕ)).mulVecLin
def sectionMap : (Fin 3 → ZMod 2) →ₗ[ZMod 2] V :=
  (binaryRectangularMatrixOfColumnMasks 8 3 (![1,2,8] : Fin 3 → ℕ)).mulVecLin
private theorem kill_basis : ∀ i : Fin 5,projection (S.inclusion (Pi.single i 1))=0 := by decide +kernel
private theorem defect_basis : ∀ i : Fin 8,
    Pi.single i 1-sectionMap (projection (Pi.single i 1))∈S.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel
private def factor : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
  (binaryRectangularMatrixOfColumnMasks 3 3 (![5,0,0] : Fin 3 → ℕ)).mulVecLin
private abbrev g := (binaryPermutationRepresentation 8) (BinaryMenuCayley8T22.generators 2)
private abbrev h := (binaryPermutationRepresentation 8) (BinaryMenuCayley8T22.generators 1)
private theorem factor_basis : ∀ i : Fin 8,
    projection (g (Pi.single i 1)-Pi.single i 1)=
      factor (projection (h (Pi.single i 1)-Pi.single i 1)) := by decide +kernel
private theorem factor_map : projection.comp (g-LinearMap.id)=
    factor.comp (projection.comp (h-LinearMap.id)) := by
  apply LinearMap.pi_ext
  intro i c
  have hs : Pi.single i c=c • Pi.single i (1 : ZMod 2) := by ext j;simp [Pi.single_apply,mul_ite]
  simp only [hs,map_smul,LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,factor_basis]

theorem projection_eq_zero_of_mem (v : V) (hv : v∈S.space) : projection v=0 := by
  have hle : S.space≤projection.ker := S.le_of_basis_mem projection.ker kill_basis
  exact hle hv

theorem mem_of_projection_eq_zero (v : V) (hv : projection v=0) : v∈S.space := by
  have hh := linear_quotient_defect_mem_of_basis S.space projection sectionMap defect_basis v
  rw [hv,map_zero,sub_zero] at hh
  exact hh

/-- This is an inclusion between two kernels in the SAME original
three-dimensional quotient, not a match of their dimensions. -/
theorem difference_kernel_inclusion (v : V)
    (hv : (binaryPermutationRepresentation 8) (BinaryMenuCayley8T22.generators 1) v-v∈S.space) :
    (binaryPermutationRepresentation 8) (BinaryMenuCayley8T22.generators 2) v-v∈S.space := by
  apply mem_of_projection_eq_zero
  have he := DFunLike.congr_fun factor_map v
  change projection (g v-v)=factor (projection (h v-v)) at he
  rw [projection_eq_zero_of_mem _ hv,map_zero] at he
  exact he
end SymmetricSubgroupAsymptotics.BinaryHeisenbergFourteenQuotientKernelInclusion
