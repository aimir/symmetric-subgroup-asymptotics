import SymmetricSubgroupAsymptotics.CFSGFFourNormCertificateSparseWords
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovFirstStep
import SymmetricSubgroupAsymptotics.SelectedFiniteFunctionTrajectory

/-! The checked intermediate root steps certify the actual ordered
linear word. This helper is applied to the literal selected first
trajectory here; later trajectories use the same proof. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightSparseTrajectory
open CFSGFFourNormCertificateSparseAction CFSGFFourNormCertificateSparseWords
open CFSGReeFFourFieldEightWordTemplates CFSGReeFFourFieldEightCertificateField
open CFSGReeFFourFieldEightKrylovData CFSGReeFFourFieldEightKrylovFirstStep

private def stepAction (i : Fin 70) : (Fin 26 → Element) → Fin 26 → Element :=
  sparseStep Element (stepLetter i).1 (stepLetter i).2.1 (ofBits (stepLetter i).2.2)

private theorem ofFn_stepAction : List.ofFn stepAction =
    selectedLetters.reverse.map (fun x => sparseStep Element x.1 x.2.1 x.2.2) := by
  have hget : List.ofFn stepLetter = rootWord.reverse := by
    change List.ofFn (rootWord.reverse.get) = rootWord.reverse
    exact List.ofFn_get rootWord.reverse
  calc
    List.ofFn stepAction = (List.ofFn stepLetter).map (fun x =>
        sparseStep Element x.1 x.2.1 (ofBits x.2.2)) :=
      by
        change List.ofFn (fun i => sparseStep Element (stepLetter i).1
          (stepLetter i).2.1 (ofBits (stepLetter i).2.2)) = _
        exact List.ofFn_comp' stepLetter (fun x : Bool × (Fin 4 × Fin 8) =>
          sparseStep Element x.1 x.2.1 (ofBits x.2.2))
    _ = _ := by
      rw [hget]
      simp only [selectedLetters, List.map_reverse, List.map_map, Function.comp_def]

theorem wordEnd_eq_last (v : Fin 71 → Fin 26 → Element)
    (hstep : ∀ i : Fin 70, sparseStep Element (stepLetter i).1 (stepLetter i).2.1
      (ofBits (stepLetter i).2.2) (v i.castSucc) = v i.succ) :
    wordEnd Element (RingHom.id Element) selectedLetters (v 0) = v (Fin.last 70) := by
  rw [wordEnd_apply_eq_foldl_reverse]
  have h := SelectedFiniteFunctionTrajectory.foldl_eq_last 70 stepAction v hstep
  rw [ofFn_stepAction, List.foldl_map] at h
  exact h

theorem first_word_action :
    wordEnd Element (RingHom.id Element) selectedLetters (vectors 0) = vectors 1 := by
  have h := wordEnd_eq_last CFSGReeFFourFieldEightKrylovFirstStep.stages
    (fun i => funext (step_certificate i))
  simpa only [stage_initial, stage_final] using h

end SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightSparseTrajectory
