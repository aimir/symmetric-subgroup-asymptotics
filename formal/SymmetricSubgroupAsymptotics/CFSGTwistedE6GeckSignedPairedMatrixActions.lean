import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPairedMatrixActions
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSelfRootConjugation

/-! The original fixed paired Weyl word sends its positive paired root
at -t to its negative paired root at t, in the SAME actual matrix group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSignedPairedMatrixActions
open CFSGTwistedE6GeckPairedMatrixActions CFSGTwistedE6GeckSourceWordAction
open CFSGTwistedE6GeckSourceAction CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6PairedFixedRoots CFSGTwistedE6FixedA2 CFSGSerreOrdinaryTwists
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoGeckSelfRootConjugation CFSGNormTwoGeckOrthogonalWeyl
open CFSGSerreQuadraticMatrix CFSGCommutatorProductCrossCommute

def matrixPairedNegativeRoot (q : CFSG.PrimePower) (j : Fin 2) (t : q.Extension 2) :
    MatrixGroup (q.Extension 2) :=
  canonicalElementaryRoot rawData (q.Extension 2) true (pairedNode j) t*
    canonicalElementaryRoot rawData (q.Extension 2) true
      (CFSG.Models.e6Twist (pairedNode j)) (t^q.order)

theorem paired_negative_action (q : CFSG.PrimePower) (j : Fin 2) (t : q.Extension 2) :
    imageAction q (pairedRoot q true j t)=
      matrixAction (q.Extension 2) (matrixPairedNegativeRoot q j t) :=
  pairedRoot_action q true j t

theorem matrixPaired_self (q : CFSG.PrimePower) (j : Fin 2) (t : q.Extension 2) :
    matrixPairedWeyl q j*matrixPairedRoot q j (-t)*(matrixPairedWeyl q j)⁻¹=
      matrixPairedNegativeRoot q j t := by
  have hc : CFSGGeckSerreRepresentation.cartan E6Base E6Index
      (pairedNode j) (CFSG.Models.e6Twist (pairedNode j))=0 := by
    rw [E6_cartan]
    exact pairedNode_cartan j
  have hc' : CFSGGeckSerreRepresentation.cartan E6Base E6Index
      (CFSG.Models.e6Twist (pairedNode j)) (pairedNode j)=0 := by
    rw [E6_cartan]
    fin_cases j <;> decide
  have hneg : (-t)^q.order= -(t^q.order) := by
    change definingFieldAutomorphism q 2 (-t)= -(definingFieldAutomorphism q 2 t)
    exact map_neg _ _
  let W (i : Fin 6) := canonicalWeyl rawData (q.Extension 2) i
  let R (i : Fin 6) (a : q.Extension 2) := canonicalRoot rawData (q.Extension 2) false i a
  apply Subtype.ext
  change (W (pairedNode j)*W (CFSG.Models.e6Twist (pairedNode j)))*
      (R (pairedNode j) (-t)*R (CFSG.Models.e6Twist (pairedNode j)) ((-t)^q.order))*
      (W (pairedNode j)*W (CFSG.Models.e6Twist (pairedNode j)))⁻¹=
    canonicalRoot rawData (q.Extension 2) true (pairedNode j) t*
      canonicalRoot rawData (q.Extension 2) true (CFSG.Models.e6Twist (pairedNode j)) (t^q.order)
  rw [hneg]
  calc
    _ = (W (pairedNode j)*R (pairedNode j) (-t)*(W (pairedNode j))⁻¹)*
        (W (CFSG.Models.e6Twist (pairedNode j))*R (CFSG.Models.e6Twist (pairedNode j))
          (-(t^q.order))*(W (CFSG.Models.e6Twist (pairedNode j)))⁻¹) := by
      symm
      exact conjugate_product_of_cross_commute _ _ _ _
        (orthogonal_weyls CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
          E6Base E6Index (q.Extension 2) _ _ hc)
        (orthogonal_weyl_root CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
          E6Base E6Index (q.Extension 2) _ _ hc' false (-t))
        (orthogonal_weyl_root CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
          E6Base E6Index (q.Extension 2) _ _ hc false (-(t^q.order)))
    _ = _ := by
      dsimp only [W,R]
      rw [self_root_word,self_root_word,neg_neg,neg_neg]

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSignedPairedMatrixActions
