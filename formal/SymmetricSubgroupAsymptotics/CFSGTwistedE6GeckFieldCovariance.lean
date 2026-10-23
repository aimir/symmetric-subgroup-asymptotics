import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckDiagramCovariance
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticFieldIntertwining
import SymmetricSubgroupAsymptotics.CFSGSerreOrdinaryTwistModels

/-! Actual diagram--field covariance for the original E6 tensor module,
including its defining quadratic-extension Frobenius. No fixed-point
surjectivity or original derived-group generation is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFieldCovariance
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreQuadraticMatrix
open CFSGTwistedE6GeckDiagramCovariance

theorem field_diagram_covariance (K : Type) [Field K] (sigma : K≃+*K)
    (x : Space CartanMatrix.E₆ K) :
    baseChange data K (spaceEquiv CartanMatrix.E₆ K e6Permutation e6_preserves
      (CFSGSerreField.semilinearEquiv CartanMatrix.E₆ K sigma x))=
      Matrix.reindexAlgEquiv K K diagramIndex (sigma.toRingHom.mapMatrix (baseChange data K x)) := by
  change baseChange data K
    (((integralEquiv CartanMatrix.E₆ e6Permutation e6_preserves).baseChange ℤ K
      (integralLattice CartanMatrix.E₆) (integralLattice CartanMatrix.E₆))
        (CFSGSerreField.semilinearEquiv CartanMatrix.E₆ K sigma x))=_
  rw [←tensor_diagram_covariance,baseChange_semilinear]

theorem defining_e6_covariance (q : CFSG.PrimePower)
    (x : Space CartanMatrix.E₆ (q.Extension 2)) :
    baseChange data (q.Extension 2)
      (spaceEquiv CartanMatrix.E₆ (q.Extension 2) e6Permutation e6_preserves
        (CFSGSerreField.semilinearEquiv CartanMatrix.E₆ (q.Extension 2)
          (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2) x))=
      Matrix.reindexAlgEquiv (q.Extension 2) (q.Extension 2) diagramIndex
        ((CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2).toRingHom.mapMatrix
          (baseChange data (q.Extension 2) x)) :=
  field_diagram_covariance (q.Extension 2) (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2) x

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFieldCovariance
