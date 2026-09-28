import SymmetricSubgroupAsymptotics.C3PhysicalOwnerAlignedContinuation
import SymmetricSubgroupAsymptotics.C1TernaryPrimeBaseCanonicalBound

/-!
# The prime-base subbranch on an aligned high-C3 cell

Once the first-owner index retains the actual selected branch property, a
degree-twelve cell is definitionally reduced to a width-twelve action.  Its
intrinsic prime-base witness can therefore feed the unconditional canonical
bound without a recognition or top-map premise.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
open TernaryA4InvariantSubmodules

/-- An aligned degree-twelve cell carrying the prime-base witness satisfies
the complete local bound required by the forward continuation. -/
theorem c3HighAligned_primeBase_local_bound
    (j : C3HighAlignedFirstOwnerIndex)
    (hkind : c3PhysicalOwnerKindEquiv j.1.2.1 =
      C3PhysicalOwnerKind.degreeTwelve)
    (W : C1TernaryPrimeBaseOwnerWitness
      (c3HighAlignedFirstOwnerAction j))
    (n : ℕ) (hn : c3HighAlignedFirstOwnerWidth j ≤ n) :
    (Nat.card (FusionWidthCanonicalFamily
      (c3HighAlignedFirstOwnerAction j) hn
      (c3HighAlignedFirstOwnerPredicate j
        (n - c3HighAlignedFirstOwnerWidth j))) : ℝ) /
        exactBenchmark n ≤
      c1EarlierKernel (n - c3HighAlignedFirstOwnerWidth j) .degreeTwelve
        (∑ N : {N : Subgroup (c3HighAlignedFirstOwnerAction j) // N.Normal},
          (originalNormalRegularConstant 3 W.top W.baseModule W.baseChart N : ℝ) *
            max 1 (Nat.card (A4 ≃* A4) : ℝ))
        (Nat.card (Subgroup.normalizer
          (c3HighAlignedFirstOwnerAction j :
            Set (Equiv.Perm (Fin (c3HighAlignedFirstOwnerWidth j))))) : ℝ) *
        ordinarySubgroupRatio (n - c3HighAlignedFirstOwnerWidth j) := by
  rcases j with ⟨⟨d, owner, i⟩, hj⟩
  have hcard := hj.2
  rw [hkind] at hcard
  change Nat.card (Fin d.width) = 12 at hcard
  simp only [Nat.card_fin] at hcard
  cases d with
  | three => simp [C3HighWidthLabel.width] at hcard
  | four => simp [C3HighWidthLabel.width] at hcard
  | six => simp [C3HighWidthLabel.width] at hcard
  | nine => simp [C3HighWidthLabel.width] at hcard
  | twelve =>
      let b := n - 12
      have hmain := W.widthCanonical_bound_internal_top
        i.representative b
        (c3HighFirstOwnerPredicate ⟨C3HighWidthLabel.twelve, owner, i⟩ b)
        (c3HighFirstOwnerPredicate_natural
          ⟨C3HighWidthLabel.twelve, owner, i⟩ b)
      have hbn : b + 12 = n := Nat.sub_add_cancel hn
      convert hmain using 1 <;>
        simp only [c3HighAlignedFirstOwnerAction,
          c3HighAlignedFirstOwnerWidth, c3HighAlignedFirstOwnerPredicate,
          c3HighFirstOwnerAction, c3HighFirstOwnerWidth,
          C3HighWidthLabel.width, b, hbn]
      congr
      all_goals
        first
        | exact proof_irrel_heq _ _
        | simpa only [b] using hbn.symm
  | twentySeven => simp [C3HighWidthLabel.width] at hcard

end SymmetricSubgroupAsymptotics

end
