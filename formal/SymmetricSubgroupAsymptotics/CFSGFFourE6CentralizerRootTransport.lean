import SymmetricSubgroupAsymptotics.CFSGFFourE6CentralizerRootPilot
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalTransport
import SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedWordClassification

/-! The selected fifteen-root subsystem transports to EVERY literal
relative-Weyl image of the highest root. Each root is oriented positively
AFTER transport; actual sign separation prevents collisions, and the
diagram orbit labels remain unchanged. No transitivity theorem for the
set of all fixed roots is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6CentralizerRootTransport
open CFSGFFourE6CentralizerRootPilot CFSGNormTwoCoordinateOrthogonalTransport
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoRootPairing
open CFSGTwistedE6WeylChamber CFSGTwistedE6FixedWordClassification
open CFSGTwistedE6DiagramRootOrthogonality CFSGExceptionalCartanPositiveDefinite
open CFSGExceptionalNormTwoBases CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckColumns

private abbrev positiveRep := positiveRepresentative CartanMatrix.E₆ CartanMatrix.E₆_diag
  CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos

theorem positiveRep_diagram (k : Roots CartanMatrix.E₆) :
    diagramRoot (positiveRep k).val=(positiveRep (diagramRoot k)).val := by
  by_cases hk : ∀i,0≤k.val i
  · have hdk : ∀i,0≤(diagramRoot k).val i := by
      intro i
      rw [diagramRoot_coordinate]
      exact hk _
    simp only [positiveRep,positiveRepresentative,dif_pos hk,dif_pos hdk]
  · have hdk : ¬∀i,0≤(diagramRoot k).val i := by
      intro h
      apply hk
      intro i
      have hi := h (CFSGSerreDiagram.e6Permutation i)
      rw [diagramRoot_coordinate,diagramPermutation_involutive] at hi
      exact hi
    simp only [positiveRep,positiveRepresentative,dif_neg hk,dif_neg hdk]
    apply Subtype.ext
    funext i
    simp only [diagramRoot_coordinate,negative_val,Pi.neg_apply]

def transportedRoot (r : List (Fin 4)) (i : Fin 15) : PositiveRoot CartanMatrix.E₆ :=
  positiveRep (rootAction (expandRelative r) (intervalRoot i).val)

def transportedHighest (r : List (Fin 4)) : Roots CartanMatrix.E₆ :=
  rootAction (expandRelative r) highestRoot

theorem transportedRoot_injective (r : List (Fin 4)) :
    Function.Injective (transportedRoot r) :=
  transported_positive_injective CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos (expandRelative r)
    intervalRoot intervalRoot_injective

theorem transportedRoot_diagram (r : List (Fin 4)) (i : Fin 15) :
    diagramRoot (transportedRoot r i).val=(transportedRoot r (partner i)).val := by
  change diagramRoot (positiveRep (rootAction (expandRelative r) (intervalRoot i).val)).val=_
  rw [positiveRep_diagram,relative_root_action_commutes,intervalRoot_diagram]
  rfl

theorem transportedHighest_diagram (r : List (Fin 4)) :
    diagramRoot (transportedHighest r)=transportedHighest r := by
  change diagramRoot (rootAction (expandRelative r) highestRoot)=_
  rw [relative_root_action_commutes,highestRoot_diagram]
  rfl

theorem transportedRoot_orthogonal (r : List (Fin 4)) (i : Fin 15) :
    CFSGIntegerMatrixPairing.integerPairing CartanMatrix.E₆
      (transportedRoot r i).val.val (transportedHighest r).val=0 := by
  have hh := wordRoot_integer_pairing CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base E6Index (expandRelative r) (intervalRoot i).val highestRoot
  rw [intervalRoot_orthogonal_highest] at hh
  rcases positiveRepresentative_val CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
      (rootAction (expandRelative r) (intervalRoot i).val) with hp|hp
  · change CFSGIntegerMatrixPairing.integerPairing CartanMatrix.E₆
      (positiveRep _).val.val (transportedHighest r).val=0
    rw [hp]
    exact hh
  · change CFSGIntegerMatrixPairing.integerPairing CartanMatrix.E₆
      (positiveRep _).val.val (transportedHighest r).val=0
    rw [hp,map_neg,LinearMap.neg_apply]
    change -CFSGIntegerMatrixPairing.integerPairing CartanMatrix.E₆
      (rootAction (expandRelative r) (intervalRoot i).val).val
      (rootAction (expandRelative r) highestRoot).val=0
    rw [hh,neg_zero]

end SymmetricSubgroupAsymptotics.CFSGFFourE6CentralizerRootTransport
