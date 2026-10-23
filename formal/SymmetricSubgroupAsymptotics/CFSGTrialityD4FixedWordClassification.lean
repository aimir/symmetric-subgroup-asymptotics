import SymmetricSubgroupAsymptotics.CFSGTrialityD4WordCancellation
import SymmetricSubgroupAsymptotics.CFSGTrialityD4CentralWordMatrix
import SymmetricSubgroupAsymptotics.CFSGTrialityRelativeWordLanguage

/-! Every literal D4 Weyl word whose actual root action commutes with
triality has the same integral action as a word in the two actual fixed
relative Weyl words. The signed central-root normalization and residual
central stabilizer are both proved from the original lattice roots. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityD4FixedWordClassification
open CFSGTrialityD4NormTwo CFSGTrialityD4InvariantRoots CFSGTrialityD4WordDiscriminant
open CFSGTrialityD4WordCancellation CFSGTrialityD4CentralWordMatrix
open CFSGTrialityRelativeWordLanguage CFSGNormTwoRootPairing
open CFSGNormTwoGeckWeylWordAlgebra

theorem exists_relative_word_action (w : List (Fin 4))
    (hcomm : ∀ k, diagramRoot (rootAction w k) = rootAction w (diagramRoot k)) :
    ∃ r : List Bool, linearAction w = linearAction (expandRelative r) := by
  have hfixed : diagramRoot (rootAction w (Index 1)) = rootAction w (Index 1) := by
    rw [hcomm, diagramRoot_index]
    rfl
  obtain ⟨neg, s, hk⟩ := fixed_root_signed_long (rootAction w (Index 1)) hfixed
  let r := relativeSignedLongWord neg s
  let v := expandRelative r
  let u := inverseWord v ++ w
  have hv : rootAction v (Index 1) = rootAction w (Index 1) :=
    (relativeSignedLongWord_root neg s).trans hk.symm
  have hvcomm : ∀ k, diagramRoot (rootAction v k) = rootAction v (diagramRoot k) :=
    relative_root_action_commutes r
  have hucomm : ∀ k, diagramRoot (rootAction u k) = rootAction u (diagramRoot k) := by
    intro k
    dsimp only [u]
    rw [rootAction_append, rootAction_append, rootAction_inverse_commutes v hvcomm, hcomm]
  have hucentral : rootAction u (Index 1) = (Index 1 : Roots (CartanMatrix.D 4)) := by
    dsimp only [u]
    rw [rootAction_append, ← hv]
    exact rootAction_inverse_left v (Index 1)
  have huLinear : linearAction u = (linearAction v)⁻¹ * linearAction w := by
    dsimp only [u]
    rw [linearAction_append, linearAction_inverseWord]
  have hcancel : linearAction v * linearAction u = linearAction w := by
    rw [huLinear, mul_inv_cancel_left]
  obtain ⟨z, hz, huz⟩ := central_fixed_relative_word u hucomm hucentral
  have hw : linearAction w = linearAction v * linearAction z :=
    hcancel.symm.trans (congrArg (fun e => linearAction v * e) huz)
  rcases hz with rfl | rfl
  · refine ⟨r, ?_⟩
    have hzero : linearAction [] = 1 := rfl
    simpa only [hzero, mul_one] using hw
  · refine ⟨r ++ [false,true,false,true,false], ?_⟩
    rw [expandRelative_append, central_stabilizer_expand, linearAction_append]
    exact hw

end SymmetricSubgroupAsymptotics.CFSGTrialityD4FixedWordClassification
