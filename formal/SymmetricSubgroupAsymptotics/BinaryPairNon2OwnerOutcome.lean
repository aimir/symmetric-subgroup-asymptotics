import SymmetricSubgroupAsymptotics.Non2OriginalFusionFaithfulCover
import SymmetricSubgroupAsymptotics.Non2OriginalFusionOwnerBridge

/-!
# Pair-axis or earlier-owner outcomes

This is the direct consumer of the remaining structural exhaustion theorem.
If an unowned literal axis supplies a physical pair frame whose unchanged top
is nonbinary, the complete original-weight payload is constructed for every
normal axis.  Otherwise the structural theorem must retain a proof that every
complete-source Goursat reconstruction is earlier-owned.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- The exact physical data required to turn one residual axis into the
checked nonbinary payload. -/
structure Non2PairAxisData (s : ℕ)
    (U : Subgroup (Equiv.Perm (Fin (2 * s))))
    (N : {N : Subgroup U // N.Normal}) where
  frame : BinaryPairFrame U (Fin s)
  [topPretransitive : MulAction.IsPretransitive frame.top.range (Fin s)]
  top_non2 : ¬ IsPGroup 2 frame.top.range

attribute [instance] Non2PairAxisData.topPretransitive

/-- Structural form of the desired axis exhaustion, before the two Tracey
inputs are used to manufacture the capacity payload. -/
inductive Non2PairAxisOrEarlier (s : ℕ)
    (U : Subgroup (Equiv.Perm (Fin (2 * s))))
    (N : {N : Subgroup U // N.Normal})
    (EarlierOwned : ∀ b, Subgroup (U × Equiv.Perm (Fin b)) → Prop) where
  | pair (data : Non2PairAxisData s U N)
  | earlier (owned : ∀ b (J : Subgroup (Equiv.Perm (Fin b)))
      (β : GroupEpimorphism J (U ⧸ N.1)),
      EarlierOwned b (fusionFullGoursatEncode N J β).1)

/-- Convert the structural pair-or-owner alternative into the exact complete
payload-or-owner outcome consumed by the residual recurrence. -/
noncomputable def Non2PairAxisOrEarlier.toFusionOutcome
    {s : ℕ} {U : Subgroup (Equiv.Perm (Fin (2 * s)))}
    {N : {N : Subgroup U // N.Normal}}
    {EarlierOwned : ∀ b, Subgroup (U × Equiv.Perm (Fin b)) → Prop}
    (O : Non2PairAxisOrEarlier s U N EarlierOwned)
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hs : 24 ≤ s) (heven : Even s) :
    Non2OriginalFusionAxisOutcome s U N EarlierOwned := by
  cases O with
  | pair data =>
      letI : MulAction.IsPretransitive data.frame.top.range (Fin s) :=
        data.topPretransitive
      let i : Fin s := ⟨0, by omega⟩
      let A := Classical.choice
        (data.frame.exists_non2OriginalFusionAxisPayload_of_arbitraryPairAxis
          N hTracey hExceptional data.top_non2 i hs heven)
      exact .capacity A
  | earlier howned =>
      exact .earlier howned

end SymmetricSubgroupAsymptotics

end
