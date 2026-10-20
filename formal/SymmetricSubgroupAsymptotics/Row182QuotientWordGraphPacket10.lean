import SymmetricSubgroupAsymptotics.Row182QuotientWordGraphData
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.Row182QuotientWordGraph
theorem packet10_code : ∀ r : Fin 30,
    permutationCode (sourceState (finProdFinEquiv ((10 : Fin 12), r))) = sourceCode (finProdFinEquiv ((10 : Fin 12), r)) := by decide +kernel
theorem packet10_step_source : ∀ (r : Fin 30) (j : Fin 9) (x : Fin 6),
    sourceState (step (finProdFinEquiv ((10 : Fin 12), r)) j) x = (sourceState (finProdFinEquiv ((10 : Fin 12), r)) * sourceGenerators j) x := by decide +kernel
theorem packet10_inverse_source : ∀ (r : Fin 30) (x : Fin 6),
    sourceState (inverse (finProdFinEquiv ((10 : Fin 12), r))) x = (sourceState (finProdFinEquiv ((10 : Fin 12), r)))⁻¹ x := by decide +kernel
theorem packet10_step_target : ∀ (r : Fin 30) (j : Fin 9) (x : Fin 6),
    targetState (step (finProdFinEquiv ((10 : Fin 12), r)) j) x = (targetState (finProdFinEquiv ((10 : Fin 12), r)) * targetGenerators j) x := by decide +kernel
theorem packet10_inverse_target : ∀ (r : Fin 30) (x : Fin 6),
    targetState (inverse (finProdFinEquiv ((10 : Fin 12), r))) x = (targetState (finProdFinEquiv ((10 : Fin 12), r)))⁻¹ x := by decide +kernel
end SymmetricSubgroupAsymptotics.Row182QuotientWordGraph
