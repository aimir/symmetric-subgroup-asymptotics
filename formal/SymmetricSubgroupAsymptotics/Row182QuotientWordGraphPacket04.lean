import SymmetricSubgroupAsymptotics.Row182QuotientWordGraphData
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.Row182QuotientWordGraph
theorem packet04_code : ∀ r : Fin 30,
    permutationCode (sourceState (finProdFinEquiv ((4 : Fin 12), r))) = sourceCode (finProdFinEquiv ((4 : Fin 12), r)) := by decide +kernel
theorem packet04_step_source : ∀ (r : Fin 30) (j : Fin 9) (x : Fin 6),
    sourceState (step (finProdFinEquiv ((4 : Fin 12), r)) j) x = (sourceState (finProdFinEquiv ((4 : Fin 12), r)) * sourceGenerators j) x := by decide +kernel
theorem packet04_inverse_source : ∀ (r : Fin 30) (x : Fin 6),
    sourceState (inverse (finProdFinEquiv ((4 : Fin 12), r))) x = (sourceState (finProdFinEquiv ((4 : Fin 12), r)))⁻¹ x := by decide +kernel
theorem packet04_step_target : ∀ (r : Fin 30) (j : Fin 9) (x : Fin 6),
    targetState (step (finProdFinEquiv ((4 : Fin 12), r)) j) x = (targetState (finProdFinEquiv ((4 : Fin 12), r)) * targetGenerators j) x := by decide +kernel
theorem packet04_inverse_target : ∀ (r : Fin 30) (x : Fin 6),
    targetState (inverse (finProdFinEquiv ((4 : Fin 12), r))) x = (targetState (finProdFinEquiv ((4 : Fin 12), r)))⁻¹ x := by decide +kernel
end SymmetricSubgroupAsymptotics.Row182QuotientWordGraph
