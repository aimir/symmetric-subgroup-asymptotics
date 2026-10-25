import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovTransition01
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovTransition02
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovTransition03
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovTransition04
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovTransition05
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovTransition06
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovTransition07
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovTransition08
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovTransition09
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovTransition10
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovTransition11
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovTransition12
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovTransition13
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovTransition14
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovTransition15
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovTransition16
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovTransition17
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovTransition18
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovTransition19
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovTransition20
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovTransition21
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovTransition22
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovTransition23
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovTransition24
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightSparseTrajectory
import SymmetricSubgroupAsymptotics.LinearMapSelectedKrylovPeriod
import Mathlib.Tactic.FinCases

/-! All25 selected transitions of the SAME70-root endomorphism are
assembled from individually checked one-transition sources. The displayed
annihilator then proves period109 on the displayed moving vector. -/
set_option autoImplicit false
set_option Elab.async false
-- The selected word has70 compositional roots; keep elaborator recursion local.
set_option maxRecDepth 4096
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovAction
open CFSGFFourNormCertificateSparseWords CFSGReeFFourFieldEightWordTemplates
open CFSGReeFFourFieldEightCertificateField CFSGReeFFourFieldEightKrylovData
open CFSGReeFFourFieldEightSparseTrajectory
open Polynomial
open scoped BigOperators

theorem consecutive : ∀ i : Fin 25,
    (wordEnd Element (RingHom.id Element) selectedLetters) (vectors i.castSucc) = vectors i.succ := by
  intro i
  fin_cases i
  · exact first_word_action
  · have h := wordEnd_eq_last CFSGReeFFourFieldEightKrylovTransition01.stages
      (fun k => funext (CFSGReeFFourFieldEightKrylovTransition01.step_certificate k))
    simpa only [CFSGReeFFourFieldEightKrylovTransition01.stage_initial,
      CFSGReeFFourFieldEightKrylovTransition01.stage_final, CFSGReeFFourFieldEightKrylovTransition01.inputIndex] using h
  · have h := wordEnd_eq_last CFSGReeFFourFieldEightKrylovTransition02.stages
      (fun k => funext (CFSGReeFFourFieldEightKrylovTransition02.step_certificate k))
    simpa only [CFSGReeFFourFieldEightKrylovTransition02.stage_initial,
      CFSGReeFFourFieldEightKrylovTransition02.stage_final, CFSGReeFFourFieldEightKrylovTransition02.inputIndex] using h
  · have h := wordEnd_eq_last CFSGReeFFourFieldEightKrylovTransition03.stages
      (fun k => funext (CFSGReeFFourFieldEightKrylovTransition03.step_certificate k))
    simpa only [CFSGReeFFourFieldEightKrylovTransition03.stage_initial,
      CFSGReeFFourFieldEightKrylovTransition03.stage_final, CFSGReeFFourFieldEightKrylovTransition03.inputIndex] using h
  · have h := wordEnd_eq_last CFSGReeFFourFieldEightKrylovTransition04.stages
      (fun k => funext (CFSGReeFFourFieldEightKrylovTransition04.step_certificate k))
    simpa only [CFSGReeFFourFieldEightKrylovTransition04.stage_initial,
      CFSGReeFFourFieldEightKrylovTransition04.stage_final, CFSGReeFFourFieldEightKrylovTransition04.inputIndex] using h
  · have h := wordEnd_eq_last CFSGReeFFourFieldEightKrylovTransition05.stages
      (fun k => funext (CFSGReeFFourFieldEightKrylovTransition05.step_certificate k))
    simpa only [CFSGReeFFourFieldEightKrylovTransition05.stage_initial,
      CFSGReeFFourFieldEightKrylovTransition05.stage_final, CFSGReeFFourFieldEightKrylovTransition05.inputIndex] using h
  · have h := wordEnd_eq_last CFSGReeFFourFieldEightKrylovTransition06.stages
      (fun k => funext (CFSGReeFFourFieldEightKrylovTransition06.step_certificate k))
    simpa only [CFSGReeFFourFieldEightKrylovTransition06.stage_initial,
      CFSGReeFFourFieldEightKrylovTransition06.stage_final, CFSGReeFFourFieldEightKrylovTransition06.inputIndex] using h
  · have h := wordEnd_eq_last CFSGReeFFourFieldEightKrylovTransition07.stages
      (fun k => funext (CFSGReeFFourFieldEightKrylovTransition07.step_certificate k))
    simpa only [CFSGReeFFourFieldEightKrylovTransition07.stage_initial,
      CFSGReeFFourFieldEightKrylovTransition07.stage_final, CFSGReeFFourFieldEightKrylovTransition07.inputIndex] using h
  · have h := wordEnd_eq_last CFSGReeFFourFieldEightKrylovTransition08.stages
      (fun k => funext (CFSGReeFFourFieldEightKrylovTransition08.step_certificate k))
    simpa only [CFSGReeFFourFieldEightKrylovTransition08.stage_initial,
      CFSGReeFFourFieldEightKrylovTransition08.stage_final, CFSGReeFFourFieldEightKrylovTransition08.inputIndex] using h
  · have h := wordEnd_eq_last CFSGReeFFourFieldEightKrylovTransition09.stages
      (fun k => funext (CFSGReeFFourFieldEightKrylovTransition09.step_certificate k))
    simpa only [CFSGReeFFourFieldEightKrylovTransition09.stage_initial,
      CFSGReeFFourFieldEightKrylovTransition09.stage_final, CFSGReeFFourFieldEightKrylovTransition09.inputIndex] using h
  · have h := wordEnd_eq_last CFSGReeFFourFieldEightKrylovTransition10.stages
      (fun k => funext (CFSGReeFFourFieldEightKrylovTransition10.step_certificate k))
    simpa only [CFSGReeFFourFieldEightKrylovTransition10.stage_initial,
      CFSGReeFFourFieldEightKrylovTransition10.stage_final, CFSGReeFFourFieldEightKrylovTransition10.inputIndex] using h
  · have h := wordEnd_eq_last CFSGReeFFourFieldEightKrylovTransition11.stages
      (fun k => funext (CFSGReeFFourFieldEightKrylovTransition11.step_certificate k))
    simpa only [CFSGReeFFourFieldEightKrylovTransition11.stage_initial,
      CFSGReeFFourFieldEightKrylovTransition11.stage_final, CFSGReeFFourFieldEightKrylovTransition11.inputIndex] using h
  · have h := wordEnd_eq_last CFSGReeFFourFieldEightKrylovTransition12.stages
      (fun k => funext (CFSGReeFFourFieldEightKrylovTransition12.step_certificate k))
    simpa only [CFSGReeFFourFieldEightKrylovTransition12.stage_initial,
      CFSGReeFFourFieldEightKrylovTransition12.stage_final, CFSGReeFFourFieldEightKrylovTransition12.inputIndex] using h
  · have h := wordEnd_eq_last CFSGReeFFourFieldEightKrylovTransition13.stages
      (fun k => funext (CFSGReeFFourFieldEightKrylovTransition13.step_certificate k))
    simpa only [CFSGReeFFourFieldEightKrylovTransition13.stage_initial,
      CFSGReeFFourFieldEightKrylovTransition13.stage_final, CFSGReeFFourFieldEightKrylovTransition13.inputIndex] using h
  · have h := wordEnd_eq_last CFSGReeFFourFieldEightKrylovTransition14.stages
      (fun k => funext (CFSGReeFFourFieldEightKrylovTransition14.step_certificate k))
    simpa only [CFSGReeFFourFieldEightKrylovTransition14.stage_initial,
      CFSGReeFFourFieldEightKrylovTransition14.stage_final, CFSGReeFFourFieldEightKrylovTransition14.inputIndex] using h
  · have h := wordEnd_eq_last CFSGReeFFourFieldEightKrylovTransition15.stages
      (fun k => funext (CFSGReeFFourFieldEightKrylovTransition15.step_certificate k))
    simpa only [CFSGReeFFourFieldEightKrylovTransition15.stage_initial,
      CFSGReeFFourFieldEightKrylovTransition15.stage_final, CFSGReeFFourFieldEightKrylovTransition15.inputIndex] using h
  · have h := wordEnd_eq_last CFSGReeFFourFieldEightKrylovTransition16.stages
      (fun k => funext (CFSGReeFFourFieldEightKrylovTransition16.step_certificate k))
    simpa only [CFSGReeFFourFieldEightKrylovTransition16.stage_initial,
      CFSGReeFFourFieldEightKrylovTransition16.stage_final, CFSGReeFFourFieldEightKrylovTransition16.inputIndex] using h
  · have h := wordEnd_eq_last CFSGReeFFourFieldEightKrylovTransition17.stages
      (fun k => funext (CFSGReeFFourFieldEightKrylovTransition17.step_certificate k))
    simpa only [CFSGReeFFourFieldEightKrylovTransition17.stage_initial,
      CFSGReeFFourFieldEightKrylovTransition17.stage_final, CFSGReeFFourFieldEightKrylovTransition17.inputIndex] using h
  · have h := wordEnd_eq_last CFSGReeFFourFieldEightKrylovTransition18.stages
      (fun k => funext (CFSGReeFFourFieldEightKrylovTransition18.step_certificate k))
    simpa only [CFSGReeFFourFieldEightKrylovTransition18.stage_initial,
      CFSGReeFFourFieldEightKrylovTransition18.stage_final, CFSGReeFFourFieldEightKrylovTransition18.inputIndex] using h
  · have h := wordEnd_eq_last CFSGReeFFourFieldEightKrylovTransition19.stages
      (fun k => funext (CFSGReeFFourFieldEightKrylovTransition19.step_certificate k))
    simpa only [CFSGReeFFourFieldEightKrylovTransition19.stage_initial,
      CFSGReeFFourFieldEightKrylovTransition19.stage_final, CFSGReeFFourFieldEightKrylovTransition19.inputIndex] using h
  · have h := wordEnd_eq_last CFSGReeFFourFieldEightKrylovTransition20.stages
      (fun k => funext (CFSGReeFFourFieldEightKrylovTransition20.step_certificate k))
    simpa only [CFSGReeFFourFieldEightKrylovTransition20.stage_initial,
      CFSGReeFFourFieldEightKrylovTransition20.stage_final, CFSGReeFFourFieldEightKrylovTransition20.inputIndex] using h
  · have h := wordEnd_eq_last CFSGReeFFourFieldEightKrylovTransition21.stages
      (fun k => funext (CFSGReeFFourFieldEightKrylovTransition21.step_certificate k))
    simpa only [CFSGReeFFourFieldEightKrylovTransition21.stage_initial,
      CFSGReeFFourFieldEightKrylovTransition21.stage_final, CFSGReeFFourFieldEightKrylovTransition21.inputIndex] using h
  · have h := wordEnd_eq_last CFSGReeFFourFieldEightKrylovTransition22.stages
      (fun k => funext (CFSGReeFFourFieldEightKrylovTransition22.step_certificate k))
    simpa only [CFSGReeFFourFieldEightKrylovTransition22.stage_initial,
      CFSGReeFFourFieldEightKrylovTransition22.stage_final, CFSGReeFFourFieldEightKrylovTransition22.inputIndex] using h
  · have h := wordEnd_eq_last CFSGReeFFourFieldEightKrylovTransition23.stages
      (fun k => funext (CFSGReeFFourFieldEightKrylovTransition23.step_certificate k))
    simpa only [CFSGReeFFourFieldEightKrylovTransition23.stage_initial,
      CFSGReeFFourFieldEightKrylovTransition23.stage_final, CFSGReeFFourFieldEightKrylovTransition23.inputIndex] using h
  · have h := wordEnd_eq_last CFSGReeFFourFieldEightKrylovTransition24.stages
      (fun k => funext (CFSGReeFFourFieldEightKrylovTransition24.step_certificate k))
    simpa only [CFSGReeFFourFieldEightKrylovTransition24.stage_initial,
      CFSGReeFFourFieldEightKrylovTransition24.stage_final, CFSGReeFFourFieldEightKrylovTransition24.inputIndex] using h

private theorem period_of_consecutive (T : Module.End Element (Fin 26 → Element))
    (hconsecutive : ∀ i : Fin 25, T (vectors i.castSucc) = vectors i.succ) :
    (T ^ 109) (vectors 0) = vectors 0 := by
  have hrel : ∑ i : Fin 26, coefficient i • vectors i = 0 := by
    funext j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      using linear_relation j
  have hdiv : (∑ i : Fin 26, monomial i.val (coefficient i)) ∣
      (Polynomial.X ^ 109 - 1 : Element[X]) := by
    change annihilator ∣ (Polynomial.X ^ 109 - 1 : Element[X])
    exact ⟨cofactor, polynomial_factorization⟩
  exact LinearMapSelectedKrylovPeriod.pow_apply_eq T 25 109
    coefficient vectors hconsecutive hrel hdiv

theorem selected_period :
    (wordEnd Element (RingHom.id Element) selectedLetters ^ 109) (vectors 0) = vectors 0 :=
  period_of_consecutive (wordEnd Element (RingHom.id Element) selectedLetters) consecutive

theorem selected_moved : (wordEnd Element (RingHom.id Element) selectedLetters) (vectors 0) ≠ vectors 0 := by
  rw [show (wordEnd Element (RingHom.id Element) selectedLetters) (vectors 0) = vectors 1 from consecutive 0]
  exact vector_moved

end SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovAction
