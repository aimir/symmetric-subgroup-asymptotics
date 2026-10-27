import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSharpFiveRigidity
import SymmetricSubgroupAsymptotics.FinitePermutationCycleSeedAssignments
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelvePresentationWords
import Mathlib.Data.Fin.VecNotation

/-! The original M12 centralizer bounded by a finite set of cycle-seed images.
The first concrete pilot is originalB, two literal four-cycles. Only finite
twelve-point period/coverage facts and144 point assignments are checked. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveCycleSeedClassBounds
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveSharpFiveRigidity FinitePermutationCycleSeedAssignments

theorem original_centralizer_card_le_assignments {r : ℕ} (a : M12)
    (base : Fin 5 ↪ Fin 12) (d : ℕ) (seed : Fin r → Fin 12)
    (covered : ∀ t, ∃ i : Fin r, ∃ n : ℕ, base t = (a.val^n) (seed i))
    (hseed : CycleSeparated a.val d seed) :
    Nat.card (Subgroup.centralizer ({a} : Set M12)) ≤ (assignments a.val d r).card :=
  centralizer_card_le_assignments M12Subgroup.subtype a base
    (fun g h he => eq_of_agree_five base g h he) d seed covered hseed

private def fourBase : Fin 5 ↪ Fin 12 where
  toFun := ![2,6,10,7,3]
  inj' := by decide +kernel

private def fourSeeds : Fin 2 → Fin 12 := ![2,3]

private theorem four_covered (t : Fin 5) :
    ∃ i : Fin 2, ∃ n : ℕ, fourBase t = (originalB.val^n) (fourSeeds i) := by
  fin_cases t
  · exact ⟨0,0,by decide +kernel⟩
  · exact ⟨0,1,by decide +kernel⟩
  · exact ⟨0,2,by decide +kernel⟩
  · exact ⟨0,3,by decide +kernel⟩
  · exact ⟨1,0,by decide +kernel⟩

private theorem four_separated : CycleSeparated originalB.val 4 fourSeeds := by
  decide +kernel

private theorem four_assignment_card : (assignments originalB.val 4 2).card = 32 := by
  decide +kernel

theorem originalB_centralizer_card_le_thirtyTwo :
    Nat.card (Subgroup.centralizer ({originalB} : Set M12)) ≤ 32 :=
  (original_centralizer_card_le_assignments originalB fourBase 4 fourSeeds
    four_covered four_separated).trans_eq four_assignment_card

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveCycleSeedClassBounds
