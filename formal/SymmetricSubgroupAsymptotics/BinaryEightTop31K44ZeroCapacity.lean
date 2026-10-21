import SymmetricSubgroupAsymptotics.BinaryEightTop31CoordinateAction
import SymmetricSubgroupAsymptotics.BinaryCoordinateGeneratorFixedCount
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryCharts

/-! ONE zero-axis joint capacity in the small31/K44 source. Only the
actual three-dimensional kernel coordinates and64 original top rows occur. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryEightTop31K44ZeroCapacity
open BinaryEightTop31CoordinateAction
open BinaryRegularEightNaturalRegistry (chart0 chart44)
private theorem fixed_count : Fintype.card {a : Fin 3 → ZMod 2 // ∀ j : Fin 3,
    rho (generators j) (chart44.inclusion a)-chart44.inclusion a ∈ chart0.space} = 2 := by
  decide +kernel
private theorem top_count : Fintype.card {r : Fin 64 // ∀ j : Fin 3,
    rho (rowEquiv r) (chart44.inclusion (Pi.single j 1))-
      chart44.inclusion (Pi.single j 1) ∈ chart0.space} = 16 := by decide +kernel

theorem coordinate_capacity :
    Nat.card {v : V // v ∈ chart44.space ∧ ∀ t : H, rho t v-v ∈ chart0.space} *
      Nat.card {t : H // ∀ v, v ∈ chart44.space → rho t v-v ∈ chart0.space} ≤ 32 := by
  have hf : Nat.card {v : V // v ∈ chart44.space ∧ ∀ t : H,
      rho t v-v ∈ chart0.space} ≤ 2 :=
    BinaryCoordinateFixedTopCardBounds.fixed_card_le_coordinate_count rho chart44 chart0
      generators 2 (by simpa only [Nat.card_eq_fintype_card] using fixed_count)
  have ht : Nat.card {t : H // ∀ v, v ∈ chart44.space → rho t v-v ∈ chart0.space} ≤ 16 := by
    simpa only [true_and] using BinaryCoordinateFixedTopCardBounds.top_card_le
      rho chart44 chart0 rowEquiv (fun _ => True) 16
      (by simpa only [Nat.card_eq_fintype_card,true_and] using top_count)
  exact (Nat.mul_le_mul hf ht).trans (by norm_num)
end SymmetricSubgroupAsymptotics.BinaryEightTop31K44ZeroCapacity
