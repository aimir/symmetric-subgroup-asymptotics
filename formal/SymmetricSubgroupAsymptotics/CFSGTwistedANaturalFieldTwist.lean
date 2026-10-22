import SymmetricSubgroupAsymptotics.CFSGTwistedAIntegralDiagram

/-! Literal Frobenius/diagram transport on the SAME original tensor image.
The final formula specializes the actual defining field automorphism of
TwistedA, but does not turn projectively fixed matrices into unitary ones
without a further scalar/derived-image argument. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
open CFSG.Models.Chevalley

theorem map_matrix_smul {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (r : ℕ) (a : R) (M : Mat R r) :
    f.mapMatrix (a • M) = f a • f.mapMatrix M := by
  ext i j
  exact map_mul f a (M i j)

theorem fieldAutomorphism_integer_matrix (K : Type) [Field K]
    (σ : K ≃+* K) (r : ℕ) (M : Mat ℤ r) :
    σ.toRingHom.mapMatrix ((Int.castRingHom K).mapMatrix M) =
      (Int.castRingHom K).mapMatrix M := by
  ext i j
  change σ (M i j : K) = (M i j : K)
  simp only [map_intCast]

theorem naturalBaseChange_field (K : Type) [Field K] (σ : K ≃+* K) (r : ℕ)
    (x : Space (CartanMatrix.A r) K) :
    CFSGSerreSquareZeroMatrix.baseChange (realizationData r) K
      (CFSGSerreField.tensorEquiv (CartanMatrix.A r) K σ x) =
      σ.toRingHom.mapMatrix
        (CFSGSerreSquareZeroMatrix.baseChange (realizationData r) K x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>
    simp only [CFSGSerreField.tensorEquiv_tmul,
      CFSGSerreSquareZeroMatrix.baseChange_tmul, map_matrix_smul,
      fieldAutomorphism_integer_matrix]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem naturalBaseChange_ordinaryTwistSpace (r : ℕ) (q : CFSG.PrimePower)
    (x : Space (CartanMatrix.A r) (q.Extension 2)) :
    CFSGSerreSquareZeroMatrix.baseChange (realizationData r) (q.Extension 2)
      (CFSGSerreDiagram.spaceEquiv (CartanMatrix.A r) (q.Extension 2) Fin.revPerm
        (CFSGSerreDiagram.typeA_reverse_preserves r)
        (CFSGSerreField.tensorEquiv (CartanMatrix.A r) (q.Extension 2)
          (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2) x)) =
      matrixDiagram (q.Extension 2) r
        ((CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2).toRingHom.mapMatrix
          (CFSGSerreSquareZeroMatrix.baseChange (realizationData r) (q.Extension 2) x)) := by
  rw [naturalBaseChange_diagram, naturalBaseChange_field]

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
