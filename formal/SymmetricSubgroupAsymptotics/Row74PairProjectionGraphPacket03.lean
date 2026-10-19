import SymmetricSubgroupAsymptotics.Row74PairProjectionGraphData
import Mathlib.Order.Fin.Basic
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row74PairProjectionGraph
theorem packet03_code : ∀ r : Fin 30,permutationCode (sourceState (finProdFinEquiv ((3 : Fin 4),r)))=rawCode (finProdFinEquiv ((3 : Fin 4),r)) := by decide +kernel
theorem packet03_step_source : ∀ (r : Fin 30) (j : Fin 4) (x : Fin 6),sourceState (embed (step (finProdFinEquiv ((3 : Fin 4),r)) j)) x=(sourceState (finProdFinEquiv ((3 : Fin 4),r))*sourceGenerators j) x := by decide +kernel
theorem packet03_inverse_source : ∀ (r : Fin 30) (x : Fin 6),sourceState (embed (inverse (finProdFinEquiv ((3 : Fin 4),r)))) x=(sourceState (finProdFinEquiv ((3 : Fin 4),r)))⁻¹ x := by decide +kernel
theorem packet03_step_target : ∀ (r : Fin 30) (j : Fin 4) (x : Fin 12),targetState (embed (step (finProdFinEquiv ((3 : Fin 4),r)) j)) x=(targetState (finProdFinEquiv ((3 : Fin 4),r))*targetGenerators j) x := by decide +kernel
theorem packet03_inverse_target : ∀ (r : Fin 30) (x : Fin 12),targetState (embed (inverse (finProdFinEquiv ((3 : Fin 4),r)))) x=(targetState (finProdFinEquiv ((3 : Fin 4),r)))⁻¹ x := by decide +kernel
end SymmetricSubgroupAsymptotics.Row74PairProjectionGraph
