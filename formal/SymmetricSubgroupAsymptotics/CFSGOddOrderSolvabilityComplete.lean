import SymmetricSubgroupAsymptotics.CFSGTrialitySelectedWeylEvenOrderRefinement

/-! The cumulative actual-model parity guard is empty.  The resulting
odd-order solvability theorem has only the pinned CFSG classification as
an input; no model-parity or solvability callback remains. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReduction

/-- Exhaustion of the literal index and sporadic constructors. -/
theorem remaining_even_order_model_after_triality_parity_false (i : CFSG.Index) :
    ¬RemainingEvenOrderModelAfterTrialityParity i := by
  intro hi
  cases i <;>
    simp [RemainingEvenOrderModelAfterTrialityParity,
      RemainingEvenOrderModelAfterTwistedAReversal,
      RemainingEvenOrderModelAfterReeAndTits,
      RemainingEvenOrderModelAfterMonster, RemainingEvenOrderModelAfterLy,
      RemainingEvenOrderModelAfterTh, RemainingEvenOrderModelAfterON,
      RemainingEvenOrderModelAfterHN, RemainingEvenOrderModelAfterSuz,
      RemainingEvenOrderModelAfterRu, RemainingEvenOrderModelAfterCoOne,
      RemainingEvenOrderModelAfterCoThree, RemainingEvenOrderModelAfterTwistedD,
      RemainingEvenOrderModelAfterTwistedE6, RemainingEvenOrderModelAfterFFour,
      RemainingEvenOrderModelAfterExceptionalE, RemainingEvenOrderModelAfterGTwo,
      RemainingEvenOrderModelAfterOrthogonalB, RemainingEvenOrderModelAfterOrthogonalD,
      RemainingEvenOrderModelAfterSymplectic, RemainingEvenOrderModelAfterSerreTwo,
      RemainingEvenOrderModelWithoutSuzuki, RemainingEvenOrderModelWithSporadics,
      RemainingEvenOrderModel, TrialityParityIndex, TwistedAReversalIndex,
      ReeAndTitsIndex, TwistedDIndex, TwistedE6Index, FFourIndex,
      ExceptionalEIndex, GTwoIndex, OrthogonalBIndex, OrthogonalDIndex,
      SymplecticIndex, CharacteristicTwoUntwistedIndex] at hi
  case sporadic s =>
    cases s <;> simp_all [SporadicEvenOrderResidual]

/-- Every inherited nonabelian simple original CFSG model has even order. -/
theorem nonabelian_simple_model_even_card (i : CFSG.Index)
    [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    Even (Nat.card i.Model) := by
  rcases evenOrder_model_or_remaining_after_triality_parity i hn with h | h
  · exact h
  · exact (remaining_even_order_model_after_triality_parity_false i h).elim

/-- Odd-order solvability follows from the pinned classification alone. -/
theorem odd_order_solvable_of_cfsg (hCFSG : CFSG.CFSGClassification)
    (G : Type) [Group G] [Finite G] (hG : Odd (Nat.card G)) : IsSolvable G := by
  apply odd_order_solvable_of_cfsg_even_models hCFSG ?_ G hG
  intro i _ _ hn
  exact nonabelian_simple_model_even_card i hn

end SymmetricSubgroupAsymptotics.CFSGReduction
