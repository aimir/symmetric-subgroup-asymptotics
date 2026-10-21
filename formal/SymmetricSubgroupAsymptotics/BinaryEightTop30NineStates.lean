import SymmetricSubgroupAsymptotics.BinaryEightTop30CoordinateAction
import SymmetricSubgroupAsymptotics.BinaryCoordinateRegistry

/-! Nine literal invariant spaces under the original8T30 action. This
file proves their invariance and chain relations, not completeness. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryEightTop30NineStates
open BinaryEightTop30CoordinateAction

def chartIndex : Fin 9 → Fin 47 := ![0,1,45,29,37,9,44,20,23]
def charts (i : Fin 9) : Σ d, BinaryCoordinateSpace 8 d :=
  BinaryRegularEightNaturalRegistry.charts (chartIndex i)
private theorem positive : ∀ (i : Fin 9) (g : Fin 3) j,
    rho (generators g) ((charts i).2.inclusion (Pi.single j 1)) ∈ (charts i).2.space := by
  decide +kernel
private theorem negative : ∀ (i : Fin 9) (g : Fin 3) j,
    rho (generators g)⁻¹ ((charts i).2.inclusion (Pi.single j 1)) ∈ (charts i).2.space := by
  decide +kernel
def states (i : Fin 9) : Subrepresentation rho :=
  (charts i).2.subrepresentationOfGenerators rho generators generators_full
    (positive i) (negative i)
@[simp] theorem states_space (i : Fin 9) :
    (states i).toSubmodule = (charts i).2.space := rfl
private theorem chain_basis : ∀ i j : Fin 9,
    (∀ b, (charts i).2.inclusion (Pi.single b 1) ∈ (charts j).2.space) ∨
    (∀ b, (charts j).2.inclusion (Pi.single b 1) ∈ (charts i).2.space) := by
  decide +kernel
theorem chain (i j : Fin 9) :
    (states i).toSubmodule ≤ (states j).toSubmodule ∨
    (states j).toSubmodule ≤ (states i).toSubmodule := by
  rcases chain_basis i j with h | h
  · exact Or.inl ((charts i).2.le_of_basis_mem _ h)
  · exact Or.inr ((charts j).2.le_of_basis_mem _ h)
theorem bottom_space : (states 0).toSubmodule = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  change x ∈ BinaryRegularEightNaturalRegistry.chart0.space at hx
  obtain ⟨c,rfl⟩ := hx
  have hc : c = 0 := Subsingleton.elim _ _
  rw [hc,map_zero]

end SymmetricSubgroupAsymptotics.BinaryEightTop30NineStates
