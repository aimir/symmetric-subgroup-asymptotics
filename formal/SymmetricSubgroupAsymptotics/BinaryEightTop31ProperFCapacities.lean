import SymmetricSubgroupAsymptotics.BinaryEightTop31ProperF26Linear
import SymmetricSubgroupAsymptotics.BinaryCoordinateFixedTopCardBounds

/-! TWO selected proper-F coordinate capacities: the original zero axis
and the constant line. The original31 top and actual augmentation kernel
are retained in each factor. These facts do not enumerate source groups. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryEightTop31ProperFCapacities
open BinaryEightTop31CoordinateAction
open BinaryEightTop31ProperFLinear (z)
open BinaryRegularEightNaturalRegistry (chart0 chart23 chart26 chart37 chart45)

theorem zero_fixed_count : Fintype.card {v : V // v ∈ chart45.space ∧
    rho z v-v ∈ chart0.space} = 16 := by decide +kernel
theorem constant_fixed_count : Fintype.card {v : V // v ∈ chart45.space ∧
    rho z v-v ∈ chart23.space} = 32 := by decide +kernel
private theorem zero_top_count : Fintype.card {i : Fin 64 // ∀ j : Fin 5,
    rho (rowEquiv i) (chart37.inclusion (Pi.single j 1))-
      chart37.inclusion (Pi.single j 1) ∈ chart0.space} = 1 := by decide +kernel
private theorem constant_top_count : Fintype.card {i : Fin 64 // ∀ j : Fin 6,
    rho (rowEquiv i) (chart26.inclusion (Pi.single j 1))-
      chart26.inclusion (Pi.single j 1) ∈ chart23.space} = 1 := by decide +kernel

theorem zero_coordinate_capacity :
    Nat.card {v : V // v ∈ chart45.space ∧ rho z v-v ∈ chart0.space} *
      Nat.card {t : H // ∀ v, v ∈ chart37.space → rho t v-v ∈ chart0.space} ≤ 16 := by
  have ht : Nat.card {t : H // ∀ v, v ∈ chart37.space → rho t v-v ∈ chart0.space} ≤ 1 := by
    simpa only [true_and] using BinaryCoordinateFixedTopCardBounds.top_card_le
      rho chart37 chart0 rowEquiv (fun _ => True) 1 (by
        simpa only [Nat.card_eq_fintype_card,true_and] using zero_top_count)
  have hf : Nat.card {v : V // v ∈ chart45.space ∧ rho z v-v ∈ chart0.space} = 16 := by
    simpa only [Nat.card_eq_fintype_card] using zero_fixed_count
  rw [hf]
  omega

theorem constant_coordinate_capacity :
    Nat.card {v : V // v ∈ chart45.space ∧ rho z v-v ∈ chart23.space} *
      Nat.card {t : H // ∀ v, v ∈ chart26.space → rho t v-v ∈ chart23.space} ≤ 32 := by
  have ht : Nat.card {t : H // ∀ v, v ∈ chart26.space → rho t v-v ∈ chart23.space} ≤ 1 := by
    simpa only [true_and] using BinaryCoordinateFixedTopCardBounds.top_card_le
      rho chart26 chart23 rowEquiv (fun _ => True) 1 (by
        simpa only [Nat.card_eq_fintype_card,true_and] using constant_top_count)
  have hf : Nat.card {v : V // v ∈ chart45.space ∧ rho z v-v ∈ chart23.space} = 32 := by
    simpa only [Nat.card_eq_fintype_card] using constant_fixed_count
  rw [hf]
  omega
end SymmetricSubgroupAsymptotics.BinaryEightTop31ProperFCapacities
