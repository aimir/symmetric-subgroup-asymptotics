import SymmetricSubgroupAsymptotics.CFSGUnitaryRankThreePairedTorusMatrix
import SymmetricSubgroupAsymptotics.CFSGUnitaryDiagonalRadicalNormalizer

/-! The actual paired torus belongs to the SAME actual radical
normalizer as the middle SU2. Its vector action retains both distinct
weights; it is not silently replaced by scalar multiplication. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGSerreOrdinaryTwists
open CFSGTwistedAUnitaryUpperArrays

private def rankThreeTorusWeights (q : CFSG.PrimePower) (a : (q.Extension 2)ˣ) :
    Fin 4 → (q.Extension 2)ˣ :=
  ![a,a⁻¹,Units.map (definingFieldAutomorphism q 2).toMonoidHom a,
    (Units.map (definingFieldAutomorphism q 2).toMonoidHom a)⁻¹]

private theorem rankThreeTorusWeights_matrix (q : CFSG.PrimePower) (a : (q.Extension 2)ˣ) :
    ((pairedTorus q 0 a).val.val : Mat (q.Extension 2) 3) =
      Matrix.diagonal (fun i => (rankThreeTorusWeights q a i : q.Extension 2)) := by
  have hv : (fun i : Fin 4 => (rankThreeTorusWeights q a i : q.Extension 2)) =
      ![(a : q.Extension 2),(a : q.Extension 2)⁻¹,definingFieldAutomorphism q 2 a,
        (definingFieldAutomorphism q 2 a)⁻¹] := by
    ext i
    fin_cases i <;> simp [rankThreeTorusWeights, Units.val_inv_eq_inv_val]
  rw [hv]
  exact rankThree_pairedTorus_matrix q a (Units.ne_zero a)

theorem rankThree_pairedTorus_mem_radicalNormalizer (q : CFSG.PrimePower)
    (a : (q.Extension 2)ˣ) : pairedTorus q 0 a ∈ unitaryRadicalNormalizer q 1 :=
  diagonal_mem_unitaryRadicalNormalizer q 1 (pairedTorus q 0 a)
    (rankThreeTorusWeights q a) (rankThreeTorusWeights_matrix q a)

def rankThreeTorusNormalizer (q : CFSG.PrimePower) (a : (q.Extension 2)ˣ) :
    unitaryRadicalNormalizer q 1 :=
  ⟨pairedTorus q 0 a, rankThree_pairedTorus_mem_radicalNormalizer q a⟩

theorem rankThreeTorusNormalizer_vector_action (q : CFSG.PrimePower)
    (a : (q.Extension 2)ˣ) (v : Multiplicative (Fin 2 → q.Extension 2)) :
    (unitaryRadicalNormalizerVectorAutHom q 1 (rankThreeTorusNormalizer q a) v).toAdd =
      ![(definingFieldAutomorphism q 2 a / a) * v.toAdd 0,
        (definingFieldAutomorphism q 2 a) ^ 2 * v.toAdd 1] := by
  funext i
  have hi := unitaryDiagonalNormalizer_vector_action q 1 (pairedTorus q 0 a)
    (rankThreeTorusWeights q a) (rankThreeTorusWeights_matrix q a) v i
  fin_cases i <;>
    simpa [rankThreeTorusNormalizer, rankThreeTorusWeights, splitEquiv, splitIndex,
      Units.val_inv_eq_inv_val,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, div_eq_mul_inv,
      pow_two, mul_comm, mul_left_comm, mul_assoc] using hi

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
