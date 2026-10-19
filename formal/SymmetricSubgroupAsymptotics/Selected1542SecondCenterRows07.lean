import SymmetricSubgroupAsymptotics.Selected1542SecondCenterRowPredicate
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
set_option maxHeartbeats 1000000 in
theorem secondCenterRows07 : ∀ r : Fin 128,
  secondCenterRow (finProdFinEquiv ((7 : Fin 8),r)) := by
  unfold secondCenterRow
  decide +kernel
end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
