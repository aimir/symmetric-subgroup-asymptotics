import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeWordEnvelope

/-! Twelve explicit triality-compatible lattice actions suffice.
The six signed central-root images and two checked central stabilizers
give a finite menu. Matrix ratios remain in enlarged D, not assumed T. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityD4FiniteWeylMenu
open CFSGTrialityD4NormTwo CFSGTrialityD4InvariantRoots CFSGTrialityD4WordDiscriminant
open CFSGTrialityGeckDiagramCovariance
open CFSGTrialityD4WordCancellation CFSGTrialityD4CentralWordMatrix
open CFSGTrialityRelativeWordLanguage CFSGNormTwoRootPairing
open CFSGNormTwoGeckWeylWordAlgebra CFSGTrialityGeckRelativeWordEnvelope
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralWord
open CFSGTrialityGeckNormalizerEnvelope

abbrev Menu := Bool×Fin 3×Bool

def menuWord (i : Menu) : List Bool :=
  relativeSignedLongWord i.1 i.2.1++if i.2.2 then [false,true,false,true,false] else []

theorem menu_card : Nat.card Menu=12 := by
  simp [Menu,Nat.card_eq_fintype_card]

theorem exists_menu_action (w : List (Fin 4))
    (hcomm : ∀k,diagramRoot (rootAction w k)=rootAction w (diagramRoot k)) :
    ∃i:Menu,linearAction w=linearAction (expandRelative (menuWord i)) := by
  have hf : diagramRoot (rootAction w (Index 1))=rootAction w (Index 1) := by
    rw [hcomm,diagramRoot_index]
    rfl
  obtain ⟨neg,s,hk⟩ := fixed_root_signed_long (rootAction w (Index 1)) hf
  let r := relativeSignedLongWord neg s
  let v := expandRelative r
  let u := inverseWord v++w
  have hv : rootAction v (Index 1)=rootAction w (Index 1) :=
    (relativeSignedLongWord_root neg s).trans hk.symm
  have hvcomm : ∀k,diagramRoot (rootAction v k)=rootAction v (diagramRoot k) :=
    relative_root_action_commutes r
  have hucomm : ∀k,diagramRoot (rootAction u k)=rootAction u (diagramRoot k) := by
    intro k
    dsimp only [u]
    rw [rootAction_append,rootAction_append,rootAction_inverse_commutes v hvcomm,hcomm]
  have hucentral : rootAction u (Index 1)=(Index 1 : Roots (CartanMatrix.D 4)) := by
    dsimp only [u]
    rw [rootAction_append,←hv]
    exact rootAction_inverse_left v (Index 1)
  have hlin : linearAction u=(linearAction v)⁻¹*linearAction w := by
    dsimp only [u]
    rw [linearAction_append,linearAction_inverseWord]
  have hc : linearAction v*linearAction u=linearAction w := by
    rw [hlin,mul_inv_cancel_left]
  obtain ⟨z,hz,huz⟩ := central_fixed_relative_word u hucomm hucentral
  have hw : linearAction w=linearAction v*linearAction z :=
    hc.symm.trans (congrArg (fun e=>linearAction v*e) huz)
  rcases hz with rfl|rfl
  · refine ⟨(neg,s,false),?_⟩
    have hz : linearAction []=1 := rfl
    simpa only [menuWord,Bool.false_eq_true,if_false,List.append_nil,hz,mul_one] using hw
  · refine ⟨(neg,s,true),?_⟩
    change linearAction w=linearAction (expandRelative (r++[false,true,false,true,false]))
    rw [expandRelative_append,central_stabilizer_expand,linearAction_append]
    exact hw

theorem exists_menu_matrix_factor (K : Type) [Field K] (w : List (Fin 4))
    (hcomm : ∀k,diagramRoot (rootAction w k)=rootAction w (diagramRoot k)) :
    ∃(i:Menu)(d:(Matrix GeckIndex GeckIndex K)ˣ),d∈diagonalNormalizer K ∧
      wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite
        Base Index K w=d*wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
          D4_positive_definite Base Index K (expandRelative (menuWord i)) := by
  obtain ⟨i,hi⟩ := exists_menu_action w hcomm
  let W := wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K
  refine ⟨i,W w*(W (expandRelative (menuWord i)))⁻¹,
    same_action_word_ratio_mem K w (expandRelative (menuWord i)) hi,?_⟩
  exact (inv_mul_cancel_right _ _).symm

end SymmetricSubgroupAsymptotics.CFSGTrialityD4FiniteWeylMenu
