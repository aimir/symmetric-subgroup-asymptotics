import SymmetricSubgroupAsymptotics.CFSGTrialityGeckDiagramCovariance
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticFieldIntertwining
import SymmetricSubgroupAsymptotics.CFSGSerreOrdinaryTwistModels

/-! Combined diagram--field covariance for the literal original D4
Serre source and its actual Geck integral image. In particular the
defining cubic-extension Frobenius and triality act compatibly on the
SAME original tensor module. No fixed/derived group equality is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFieldCovariance
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreQuadraticMatrix
open CFSGTrialityGeckDiagramCovariance
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)):=Classical.decEq _

theorem field_diagram_covariance (K : Type) [Field K] (σ : K ≃+* K)
    (x : Space (CartanMatrix.D 4) K) :
    baseChange data K (spaceEquiv (CartanMatrix.D 4) K trialityPermutation triality_preserves
      (CFSGSerreField.semilinearEquiv (CartanMatrix.D 4) K σ x))=
      Matrix.reindexAlgEquiv K K trialityIndex (σ.toRingHom.mapMatrix (baseChange data K x)) := by
  change baseChange data K
    (((integralEquiv (CartanMatrix.D 4) trialityPermutation triality_preserves).baseChange ℤ K
      (integralLattice (CartanMatrix.D 4)) (integralLattice (CartanMatrix.D 4)))
        (CFSGSerreField.semilinearEquiv (CartanMatrix.D 4) K σ x))=_
  rw [←tensor_triality_covariance,baseChange_semilinear]

theorem defining_triality_covariance (q : CFSG.PrimePower)
    (x : Space (CartanMatrix.D 4) (q.Extension 3)) :
    baseChange data (q.Extension 3)
      (spaceEquiv (CartanMatrix.D 4) (q.Extension 3) trialityPermutation triality_preserves
        (CFSGSerreField.semilinearEquiv (CartanMatrix.D 4) (q.Extension 3)
          (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 3) x))=
      Matrix.reindexAlgEquiv (q.Extension 3) (q.Extension 3) trialityIndex
        ((CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 3).toRingHom.mapMatrix
          (baseChange data (q.Extension 3) x)) :=
  field_diagram_covariance (q.Extension 3) (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 3) x

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFieldCovariance
