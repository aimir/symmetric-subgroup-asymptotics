import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrixInvolution

/-! The literal signed anti-diagonal diagram map commutes with changing
the coefficient ring. This is needed before integral/tensor descent;
it is not a fixed-point or unitary identification hypothesis. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : ℕ)

theorem signedReversalUnit_apply (R : Type*) [CommRing R] (r : ℕ)
    (i j : Fin (r + 1)) :
    (signedReversalUnit R r : Mat R r) i j =
      if i.rev = j then signWeight R r i else 0 := by
  rw [signedReversalUnit_val]
  simp [Matrix.diagonal_mul, Matrix.submatrix_apply, Matrix.one_apply, mul_ite]

theorem map_signWeight (i : Fin (r + 1)) :
    f (signWeight R r i) = signWeight S r i := by
  simp only [signWeight, map_pow, map_neg, map_one]

theorem map_signedReversalUnit_val :
    f.mapMatrix (signedReversalUnit R r : Mat R r) = (signedReversalUnit S r : Mat S r) := by
  ext i j
  change f ((signedReversalUnit R r : Mat R r) i j) =
    (signedReversalUnit S r : Mat S r) i j
  simp only [signedReversalUnit_apply, apply_ite, map_signWeight, map_zero]
  by_cases h : i.rev = j <;> simp only [h, if_true, if_false]

theorem map_signedReversalUnit_inv_val :
    f.mapMatrix (↑((signedReversalUnit R r)⁻¹) : Mat R r) =
      (↑((signedReversalUnit S r)⁻¹) : Mat S r) := by
  have hu : Units.map f.mapMatrix.toMonoidHom (signedReversalUnit R r) =
      signedReversalUnit S r := Units.ext (map_signedReversalUnit_val f r)
  exact congrArg (fun u : (Mat S r)ˣ => (↑(u⁻¹) : Mat S r)) hu

theorem map_matrixDiagram (X : Mat R r) :
    f.mapMatrix (matrixDiagram R r X) = matrixDiagram S r (f.mapMatrix X) := by
  change f.mapMatrix ((signedReversalUnit R r : Mat R r) * (-X.transpose) *
      (↑((signedReversalUnit R r)⁻¹) : Mat R r)) =
    (signedReversalUnit S r : Mat S r) * (-(f.mapMatrix X).transpose) *
      (↑((signedReversalUnit S r)⁻¹) : Mat S r)
  have ht : f.mapMatrix X.transpose = (f.mapMatrix X).transpose := Matrix.transpose_map
  rw [map_mul, map_mul, map_neg, map_signedReversalUnit_val,
    map_signedReversalUnit_inv_val, ht]

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
