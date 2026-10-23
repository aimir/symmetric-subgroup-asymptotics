import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalRootLineNontrivial
import SymmetricSubgroupAsymptotics.CFSGFFourE6CentralizerRootPilot

/-! The literal dominant diagram-fixed E6 root defines a nontrivial
proper subgroup of the ORIGINAL F4 model, with an actual fixed-upper
conjugate-family cover and no remaining root-label premises. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalHighestRootLine
open CFSGNormTwoRootPairing CFSGIntegerMatrixPairing CFSGTwistedE6WeylChamber
open CFSGFFourE6OriginalRootFamily CFSGFFourE6OriginalRootLineNontrivial
open CFSGFFourE6FixedPositiveProjection CFSGTwistedE6GeckFixedRootFamilyCover
open CFSGTwistedE6GeckRelativeRootGenerated CFSG.Models.Chevalley

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

abbrev originalHighestRootLine (K : Type) [Field K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] := originalRootLine K theta

theorem originalHighestRootLine_ne_bot (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    originalHighestRootLine K≠⊥ :=
  positive_fixed_originalRootLine_ne_bot K p theta theta_positive theta_diagram

theorem originalHighestRootLine_ne_top (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    originalHighestRootLine K≠⊤ := originalRootLine_ne_top K p theta theta_positive

theorem original_highest_family_cover (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (g : Projective CartanMatrix.F₄ K) :
    ∃k : relativeRootMenu theta, ∃u : signedFixed K (RingEquiv.refl K) false,
      (originalHighestRootLine K).map (MulAut.conj g).toMonoidHom=
        (originalRootLine K k.val).map (MulAut.conj (fixedPositiveToOriginal K p u)).toMonoidHom :=
  original_fixed_root_family_cover K p theta theta_positive theta_dominant g

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalHighestRootLine
