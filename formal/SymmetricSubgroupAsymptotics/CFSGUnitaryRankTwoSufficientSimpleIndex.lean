import SymmetricSubgroupAsymptotics.CFSGUnitarySquareSufficientSimpleIndex
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoOuterBudget

/-! The rank-two unitary tag leaves the sufficient simple-index
residual entirely. Higher unitary ranks retain their actual outer-order
budget obligation; every other surviving model obligation is unchanged. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure CFSGTwistedAUnitaryCoordinates

def RemainingSufficientSimpleIndexAfterUnitaryRankTwo : CFSG.Index → Prop
  | .twistedA r _ _ _ => r ≠ 2
  | i => RemainingSufficientSimpleIndexAfterExceptionalE i

theorem modelBounds_or_remaining_after_unitary_rankTwo (i : CFSG.Index)
    [Finite i.Model] [IsSimpleGroup i.Model] (hn : ¬ IsMulCommutative i.Model) :
    ModelBoundsAfterUnitarySquare i ∨ RemainingSufficientSimpleIndexAfterUnitaryRankTwo i := by
  cases i <;> try exact sufficientSimpleIndex_model_or_remaining_after_exceptional_E _ hn
  case twistedA r q hr hsmall hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.TwistedA r q) := hsimple
    by_cases htwo : r = 2
    · subst r
      left
      intro ell hell
      have hq2 : 2 ≤ q.order := q.prime_isPrime.two_le.trans
        (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
      exact twistedA_rankTwo_sufficient_outer_budget q (by have := hsmall rfl; omega) ell hell
    · exact Or.inr htwo

theorem sufficientSimpleIndexBounds_of_cfsg_after_unitary_rankTwo
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterUnitaryRankTwo i →
        ModelBoundsAfterUnitarySquare i) : SufficientSimpleIndexBounds := by
  apply sufficientSimpleIndexBounds_of_cfsg_after_unitary_square hCFSG
  intro i _ _ hn _
  rcases modelBounds_or_remaining_after_unitary_rankTwo i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
