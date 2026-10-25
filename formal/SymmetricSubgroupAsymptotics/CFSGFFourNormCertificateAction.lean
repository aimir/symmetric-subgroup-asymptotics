import SymmetricSubgroupAsymptotics.CFSGFFourNormCertificateSparseAction
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Algebra.Group.Action.End

/-! The sparse coordinate action is a genuine action of the same folded
original model. Reindexing preserves the already proved actual norm
matrix homomorphism. No separate finite group is recognized here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourNormCertificateAction
open CFSGFFourE6NormMatrixAction CFSGFFourE6CharacteristicTwoNormImage
open CFSGFFourNormCertificateCoordinates CFSGFFourNormCertificateRootOperators
open CFSGFFourNormCertificateSparseAction CFSGFFourE6NormPairRepresentatives
open CFSGSerreQuadraticMatrix CFSGFFourSerreMatrices
private instance : DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _
private instance : Fintype PairIndex := by unfold PairIndex; infer_instance
private instance : DecidableEq PairIndex := Classical.decEq _

def matrixAction (K : Type) [Field K] [CharP K 2] :
    canonicalElementaryGroup realizationData K →* Matrix (Fin 26) (Fin 26) K :=
  (Matrix.reindexAlgEquiv K K coordinateEquiv.symm).toMonoidHom.comp (normMatrixAction K)

theorem matrixAction_root (K : Type) [Field K] [CharP K 2]
    (neg : Bool) (i : Fin 4) (t : K) :
    matrixAction K (foldedRoot K neg i t) = rootOperator K neg i t := by
  ext j k
  exact actual_root_entry K neg i t j k

def linearAction (K : Type) [Field K] [CharP K 2] :
    canonicalElementaryGroup realizationData K →* Module.End K (Fin 26 → K) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin 26) (Fin 26) K ≃ₐ[K]
    Module.End K (Fin 26 → K)).toMonoidHom.comp (matrixAction K)

theorem linearAction_root_apply (K : Type) [Field K] [CharP K 2]
    (neg : Bool) (i : Fin 4) (t : K) (v : Fin 26 → K) :
    linearAction K (foldedRoot K neg i t) v = sparseStep K neg i t v := by
  change (matrixAction K (foldedRoot K neg i t)).mulVec v = _
  rw [matrixAction_root, ← sparseStep_eq_mulVec]

def vectorAction (K : Type) [Field K] [CharP K 2] :
    canonicalElementaryGroup realizationData K →* Function.End (Fin 26 → K) where
  toFun g := fun v => linearAction K g v
  map_one' := by
    funext v
    change linearAction K 1 v = v
    rw [map_one]
    rfl
  map_mul' g h := by
    funext v
    change linearAction K (g*h) v = linearAction K g (linearAction K h v)
    rw [map_mul]
    rfl

end SymmetricSubgroupAsymptotics.CFSGFFourNormCertificateAction
