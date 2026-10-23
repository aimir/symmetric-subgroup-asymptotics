import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRootLineNontrivial
import SymmetricSubgroupAsymptotics.CFSGFFourE6CentralizerRootPilot

/-! The shared literal dominant E6 root gives a nontrivial proper root
line of the ORIGINAL twisted model, and an unconditional original-group
conjugate-family cover with at most 512 seed labels. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalHighestRootLine
open CFSGNormTwoRootPairing CFSGIntegerMatrixPairing CFSGTwistedE6WeylChamber
open CFSGTwistedE6GeckOriginalRootFamily CFSGTwistedE6GeckOriginalRootLineNontrivial
open CFSGTwistedE6GeckFixedRootFamilyCover CFSGTwistedE6GeckFixedPositiveProjection
open CFSGTwistedE6GeckRelativeRootGenerated CFSGSerreOrdinaryTwists

abbrev theta := CFSGFFourE6CentralizerRootPilot.highestRoot

theorem theta_positive : ∀i,0≤theta.val i := by
  intro i
  fin_cases i <;> decide

theorem theta_dominant :
    ∀i,0 ≤ integerPairing CartanMatrix.E₆ theta.val (Pi.single i (1 : ℤ) : Fin 6→ℤ) := by
  intro i
  fin_cases i <;> decide

theorem theta_diagram : diagramRoot theta=theta :=
  CFSGFFourE6CentralizerRootPilot.highestRoot_diagram

abbrev originalHighestRootLine (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] := originalRootLine q theta

theorem originalHighestRootLine_ne_bot (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] : originalHighestRootLine q≠⊥ :=
  positive_fixed_originalRootLine_ne_bot q theta theta_positive theta_diagram

theorem originalHighestRootLine_ne_top (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] : originalHighestRootLine q≠⊤ :=
  originalRootLine_ne_top q theta theta_positive

theorem original_highest_family_cover (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (g : CFSG.Models.TwistedE6 q) :
    ∃k : relativeRootMenu theta,
      ∃u : signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) false,
        (originalHighestRootLine q).map (MulAut.conj g).toMonoidHom=
          (originalRootLine q k.val).map (MulAut.conj (fixedPositiveToOriginal q u)).toMonoidHom :=
  original_fixed_root_family_cover q theta theta_positive theta_dominant g

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalHighestRootLine
