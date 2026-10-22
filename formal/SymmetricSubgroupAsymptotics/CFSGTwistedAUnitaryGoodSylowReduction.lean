import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryModelGoodSylow
import SymmetricSubgroupAsymptotics.CFSGTwistedA2GoodSylowReduction

/-! The WHOLE literal twisted-A branch leaves the exact good-Sylow
residual. Its rank-two small guard is used exactly as stated by the
classifier; every higher rank includes all prime powers, including2.
Every other previously remaining model is retained explicitly. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReduction

theorem twistedA_goodSylowPrime (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (hsmall : r = 2 → q.order ≠ 2) :
    GoodSylowPrime (CFSG.Models.TwistedA r q) q.prime := by
  by_cases htwo : r = 2
  · subst r
    exact twistedA2_goodSylowPrime q (hsmall rfl)
  · exact twistedA_higher_goodSylowPrime r (by omega) q

def RemainingGoodSylowIndexWithoutClassicalSuzukiEAndA5AndTwistedA : CFSG.Index → Prop
  | .twistedA _ _ _ _ => False
  | i => RemainingGoodSylowIndexWithoutClassicalSuzukiEAndA5 i

theorem model_goodSylow_or_remaining_without_classical_suzuki_E_A5_twistedA (i : CFSG.Index)
    [Finite i.Model] [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model) :
    (∃ p, GoodSylowPrime i.Model p) ∨
      RemainingGoodSylowIndexWithoutClassicalSuzukiEAndA5AndTwistedA i := by
  cases i <;> try exact model_goodSylow_or_remaining_without_classical_suzuki_E_A5 _ hn
  case twistedA r q hr hsmall hfinite hsimple =>
    exact Or.inl ⟨q.prime, twistedA_goodSylowPrime r hr q hsmall⟩

theorem aschbacherGuralnick_of_cfsg_and_remaining_without_classical_suzuki_E_A5_twistedA
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model →
        RemainingGoodSylowIndexWithoutClassicalSuzukiEAndA5AndTwistedA i →
          ∃ p, GoodSylowPrime i.Model p) :
    MarkedC4.PublishedAschbacherGuralnickSolubleGeneration := by
  apply aschbacherGuralnick_of_cfsg_goodSylow_models hCFSG
  intro i _ _ hn
  rcases model_goodSylow_or_remaining_without_classical_suzuki_E_A5_twistedA i hn with h | h
  · exact h
  · exact remaining i hn h

end SymmetricSubgroupAsymptotics.CFSGReduction
