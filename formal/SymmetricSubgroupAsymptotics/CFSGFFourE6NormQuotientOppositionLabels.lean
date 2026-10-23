import SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientRootMatching
import SymmetricSubgroupAsymptotics.CFSGNormTwoRootNegation

/-! Actual root negation is compatible with the norm/quotient label matching.
The finite certificates use only the 24 selected root representatives.
No group faithfulness or original F4 correspondence is asserted. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientOppositionLabels
open CFSGFFourE6NormPairRepresentatives CFSGFFourE6FixedIndexRepresentatives
open CFSGFFourE6NormQuotientRootMatching

theorem negativeTwist_mem : ∀v∈rootRepresentatives,-twistVector v∈rootRepresentatives :=
  by decide +kernel

theorem negativeTwist_twice : ∀v∈rootRepresentatives,
    -twistVector (-twistVector v)=v := by decide +kernel

theorem twist_negativeTwist : ∀v∈rootRepresentatives,
    twistVector (-twistVector v)= -v := by decide +kernel

theorem dualRoot_negativeTwist : ∀v∈rootRepresentatives,
    dualRoot (-twistVector v)= -dualRoot v := by decide +kernel

noncomputable section
open scoped Classical
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
open CFSGNormTwoGeckColumns CFSGNormTwoRootNegation CFSGSerreDiagram
open CFSGTwistedE6DiagramRootOrthogonality CFSGTwistedE6WeylChamber

def negativePair : PairIndex→PairIndex
  | .inl i=>.inl i
  | .inr r=>.inr ⟨-twistVector r.val,negativeTwist_mem r.val r.property⟩

theorem negativePair_involutive : Function.Involutive negativePair := by
  intro j
  cases j with
  | inl i=>rfl
  | inr r=>
    apply congrArg Sum.inr
    apply Subtype.ext
    exact negativeTwist_twice r.val r.property

def oppositionIndex : Equiv.Perm GeckIndex :=
  Equiv.sumCongr (Equiv.refl E6Base.support)
    (Function.Involutive.toPerm
      (negativeIndex CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite)
      (negative_negative CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite))

theorem oppositionIndex_inl (i:E6Base.support) :
    oppositionIndex (Sum.inl i)=Sum.inl i := rfl

theorem oppositionIndex_inr (r:Roots CartanMatrix.E₆) :
    oppositionIndex (Sum.inr r)=Sum.inr
      (negativeIndex CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite r) := rfl

theorem oppositionIndex_involutive : Function.Involutive oppositionIndex := by
  intro j
  cases j with
  | inl i=>rfl
  | inr r=>
    change (Sum.inr (negativeIndex CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      (negativeIndex CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite r)):GeckIndex)=Sum.inr r
    rw [negative_negative]

theorem oppositionIndex_diagram (j:GeckIndex) :
    oppositionIndex (diagramIndex j)=diagramIndex (oppositionIndex j) := by
  cases j with
  | inl i=>rfl
  | inr r=>
    change (Sum.inr (negativeIndex CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      (diagramRoot r)):GeckIndex)=Sum.inr
        (diagramRoot (negativeIndex CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite r))
    apply congrArg (fun k:Roots CartanMatrix.E₆=>(Sum.inr k:GeckIndex))
    apply Subtype.ext
    funext i
    simp only [negative_val,Pi.neg_apply,diagramRoot_coordinate]

theorem opposition_selected_inl (i:Fin 2) :
    oppositionIndex (selectedRepresentative (Sum.inl i))=selectedRepresentative (negativePair (Sum.inl i)) := rfl

theorem opposition_selected_inr (r:rootRepresentatives) :
    oppositionIndex (selectedRepresentative (Sum.inr r))=
      diagramIndex (selectedRepresentative (negativePair (Sum.inr r))) := by
  change (Sum.inr (negativeIndex CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
    ⟨r.val,rootRepresentatives_norm r.val r.property⟩):GeckIndex)=Sum.inr
      (diagramRoot ⟨-twistVector r.val,rootRepresentatives_norm _ (negativeTwist_mem r.val r.property)⟩)
  apply congrArg (fun k:Roots CartanMatrix.E₆=>(Sum.inr k:GeckIndex))
  apply Subtype.ext
  funext i
  rw [negative_val,diagramRoot_coordinate,e6Permutation_apply]
  exact congrFun (twist_negativeTwist r.val r.property).symm i

private def fixedDualRoot (r:rootRepresentatives) : Roots CartanMatrix.E₆ :=
  ⟨dualRoot r.val,fixedRootMenu_norm _ (dualRoot_mem r.val r.property)⟩

private theorem fixed_dual_representative (r:rootRepresentatives) :
    fixedRepresentative (basisIndexDual (Sum.inr r))=(Sum.inr (fixedDualRoot r):GeckIndex) := rfl

theorem opposition_fixed_dual (j:PairIndex) :
    oppositionIndex (fixedRepresentative (basisIndexDual j))=
      fixedRepresentative (basisIndexDual (negativePair j)) := by
  cases j with
  | inl i=>rfl
  | inr r=>
    change oppositionIndex (fixedRepresentative (basisIndexDual (Sum.inr r)))=
      fixedRepresentative (basisIndexDual (Sum.inr
        (⟨-twistVector r.val,negativeTwist_mem r.val r.property⟩:rootRepresentatives)))
    rw [fixed_dual_representative,fixed_dual_representative,oppositionIndex_inr]
    apply congrArg (fun k:Roots CartanMatrix.E₆=>(Sum.inr k:GeckIndex))
    apply Subtype.ext
    rw [negative_val]
    exact (dualRoot_negativeTwist r.val r.property).symm

end
end SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientOppositionLabels
