import SymmetricSubgroupAsymptotics.CFSGFFourE6RootFrameCardinality
import SymmetricSubgroupAsymptotics.CFSGFFourE6RelativeWeylFrameFaithful
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeWordEnvelope

/-! Actual folded E6 Weyl actions inject into orthogonal four-root frames.
Successive frame fibres give at most 1152 actions. A representative word
is chosen for each actual action, and equal-action matrix ratios remain
in the enlarged simultaneous normalizer. No torus recognition is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6FiniteWeylMenu
open CFSGFFourE6FixedRootFramePilot CFSGFFourE6RootFrameCardinality
open CFSGFFourE6RelativeWeylFrameFaithful CFSGTwistedE6WeylChamber
open CFSGTwistedE6FixedWordClassification CFSGTwistedE6GeckRelativeWordEnvelope
open CFSGNormTwoRootPairing CFSGNormTwoGeckWeylLatticeLinear
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckNormalizerEnvelope
open CFSGNormTwoGeckIntegralWord CFSGNormTwoGeckWeylWordDegree CFSGSerreDiagram

private instance rootFrames_fintype : Fintype RootFrames := by
  unfold CFSGFFourE6RootFrameCardinality.RootFrames FiniteOrthogonalFrameCardinality.Frames
  infer_instance

private theorem frame_twist : ∀i:Fin 4,∀j:Fin 6,
    frame i (CFSG.Models.e6Twist j)=frame i j := by decide +kernel

private theorem frame_diagram_fixed (i:Fin 4) : diagramRoot (frameRoot i)=frameRoot i := by
  apply Subtype.ext
  funext j
  change frame i (e6Permutation.symm j)=frame i j
  have hh := frame_twist i (e6Permutation.symm j)
  change frame i (e6Permutation (e6Permutation.symm j))=frame i (e6Permutation.symm j) at hh
  rw [Equiv.apply_symm_apply] at hh
  exact hh.symm

theorem frame_image_mem (r:List (Fin 4)) (i:Fin 4) :
    (rootAction (expandRelative r) (frameRoot i)).val∈menu := by
  let x := rootAction (expandRelative r) (frameRoot i)
  refine Finset.mem_filter.mpr ⟨?_,?_⟩
  · exact CFSGNormTwoCoordinateFiniteRootMenu.root_mem_menu CartanMatrix.E₆
      CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite
      CartanMatrix.E₆_off_diag_nonpos CFSGE6FiniteRootMenu.menu
      CFSGE6FiniteRootMenu.negative_simple_mem CFSGE6FiniteRootMenu.reflection_closed x
  · have hd : diagramRoot x=x := by
      change diagramRoot (rootAction (expandRelative r) (frameRoot i))=_
      rw [relative_root_action_commutes,frame_diagram_fixed]
    intro j
    have hh := congrArg (fun k:Roots CartanMatrix.E₆=>k.val (e6Permutation j)) hd
    change x.val (e6Permutation.symm (e6Permutation j))=x.val (e6Permutation j) at hh
    rw [Equiv.symm_apply_apply] at hh
    exact hh.symm

def frameImage (r:List (Fin 4)) (i:Fin 4) : menu :=
  ⟨(rootAction (expandRelative r) (frameRoot i)).val,frame_image_mem r i⟩

theorem frameImage_orthogonal (r:List (Fin 4)) (i j:Fin 4) (hij:i≠j) :
    Orth (frameImage r i) (frameImage r j) := by
  have hh := wordRoot_integer_pairing CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base E6Index (expandRelative r) (frameRoot i) (frameRoot j)
  exact hh.trans (frame_orthogonal i j hij)

def wordFrame (r:List (Fin 4)) : RootFrames :=
  ⟨frameImage r 0,⟨frameImage r 1,frameImage_orthogonal r 0 1 (by decide)⟩,
    ⟨frameImage r 2,frameImage_orthogonal r 0 2 (by decide),frameImage_orthogonal r 1 2 (by decide)⟩,
    ⟨frameImage r 3,frameImage_orthogonal r 0 3 (by decide),
      frameImage_orthogonal r 1 3 (by decide),frameImage_orthogonal r 2 3 (by decide)⟩⟩

def relativeWeylRange := Set.range (fun r:List (Fin 4)=>linearAction (expandRelative r))

def representative (i:relativeWeylRange) : List (Fin 4) := Classical.choose i.property

theorem representative_action (i:relativeWeylRange) :
    linearAction (expandRelative (representative i))=i.val := Classical.choose_spec i.property

def actionFrame (i:relativeWeylRange) : RootFrames := wordFrame (representative i)

theorem actionFrame_injective : Function.Injective actionFrame := by
  intro x y he
  have hh : ∀i:Fin 4,rootAction (expandRelative (representative x)) (frameRoot i)=
      rootAction (expandRelative (representative y)) (frameRoot i) := by
    intro i
    apply Subtype.ext
    fin_cases i
    · exact congrArg (fun f:RootFrames=>f.1.val) he
    · exact congrArg (fun f:RootFrames=>f.2.1.val.val) he
    · exact congrArg (fun f:RootFrames=>f.2.2.1.val.val) he
    · exact congrArg (fun f:RootFrames=>f.2.2.2.val.val) he
  have hlin := linearAction_eq_of_frame_eq
    (expandRelative (representative x)) (expandRelative (representative y)) hh
  apply Subtype.ext
  exact (representative_action x).symm.trans (hlin.trans (representative_action y))

instance : Finite relativeWeylRange := Finite.of_injective actionFrame actionFrame_injective

theorem relativeWeylRange_card_le : Nat.card relativeWeylRange≤1152 :=
  (Nat.card_le_card_of_injective actionFrame actionFrame_injective).trans rootFrames_card_le

theorem exists_menu_action (w:List (Fin 6))
    (hcomm:∀k,diagramRoot (rootAction w k)=rootAction w (diagramRoot k)) :
    ∃i:relativeWeylRange,linearAction w=linearAction (expandRelative (representative i)) := by
  obtain ⟨r,hr⟩ := exists_relative_word_action w hcomm
  let i:relativeWeylRange := ⟨linearAction (expandRelative r),r,rfl⟩
  exact ⟨i,hr.trans (representative_action i).symm⟩

theorem exists_menu_matrix_factor (K:Type) [Field K] (w:List (Fin 6))
    (hcomm:∀k,diagramRoot (rootAction w k)=rootAction w (diagramRoot k)) :
    ∃(i:relativeWeylRange)(d:(Matrix GeckIndex GeckIndex K)ˣ),d∈diagonalNormalizer K∧
      wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K w=
        d*wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K
          (expandRelative (representative i)) := by
  obtain ⟨i,hi⟩ := exists_menu_action w hcomm
  let W := wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K
  exact ⟨i,W w*(W (expandRelative (representative i)))⁻¹,
    same_action_word_ratio_mem K w (expandRelative (representative i)) hi,
    (inv_mul_cancel_right _ _).symm⟩

end SymmetricSubgroupAsymptotics.CFSGFFourE6FiniteWeylMenu
