import SymmetricSubgroupAsymptotics.CFSGTrialityD4CentralWordStabilizer

/-! Cancellation and diagram commutation for literal inverse Weyl words,
derived from their actual integral linear equivalences. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityD4WordCancellation
open CFSGTrialityD4NormTwo CFSGTrialityD4InvariantRoots CFSGTrialityD4WordDiscriminant
open CFSGTrialityD4CentralWordStabilizer CFSGNormTwoRootPairing
open CFSGNormTwoGeckWeylWordAlgebra CFSGNormTwoGeckWeylLatticeLinear

theorem rootAction_append (u v : List (Fin 4)) (k : Roots (CartanMatrix.D 4)) :
    rootAction (u ++ v) k = rootAction u (rootAction v k) :=
  wordRoot_append (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index u v k

theorem linearAction_append (u v : List (Fin 4)) :
    linearAction (u ++ v) = linearAction u * linearAction v :=
  wordLinear_append (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index u v

theorem linearAction_inverseWord (w : List (Fin 4)) :
    linearAction (inverseWord w) = (linearAction w)⁻¹ :=
  wordLinear_inverseWord (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index w

theorem rootAction_inverse_right (w : List (Fin 4)) (k : Roots (CartanMatrix.D 4)) :
    rootAction w (rootAction (inverseWord w) k) = k := by
  apply Subtype.ext
  calc
    _ = linearAction w (rootAction (inverseWord w) k).val :=
      (wordLinear_root (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index w (rootAction (inverseWord w) k)).symm
    _ = linearAction w (linearAction (inverseWord w) k.val) :=
      congrArg (linearAction w) (wordLinear_root (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index (inverseWord w) k).symm
    _ = k.val := by
      rw [linearAction_inverseWord]
      exact (linearAction w).apply_symm_apply k.val

theorem rootAction_inverse_left (w : List (Fin 4)) (k : Roots (CartanMatrix.D 4)) :
    rootAction (inverseWord w) (rootAction w k) = k := by
  apply rootAction_injective w
  exact rootAction_inverse_right w (rootAction w k)

theorem rootAction_inverse_commutes (w : List (Fin 4))
    (hcomm : ∀ k, diagramRoot (rootAction w k) = rootAction w (diagramRoot k))
    (k : Roots (CartanMatrix.D 4)) :
    diagramRoot (rootAction (inverseWord w) k) = rootAction (inverseWord w) (diagramRoot k) := by
  apply rootAction_injective w
  calc
    _ = diagramRoot (rootAction w (rootAction (inverseWord w) k)) := (hcomm _).symm
    _ = diagramRoot k := congrArg diagramRoot (rootAction_inverse_right w k)
    _ = rootAction w (rootAction (inverseWord w) (diagramRoot k)) :=
      (rootAction_inverse_right w (diagramRoot k)).symm

end SymmetricSubgroupAsymptotics.CFSGTrialityD4WordCancellation
