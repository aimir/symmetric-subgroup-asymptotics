import SymmetricSubgroupAsymptotics.Selected1542SecondCenterRowPredicate
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
set_option maxHeartbeats 1000000 in
theorem secondCenterRows04 : ∀ r : Fin 128,
  secondCenterRow (finProdFinEquiv ((4 : Fin 8),r)) := by
  unfold secondCenterRow
  decide +kernel
end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
