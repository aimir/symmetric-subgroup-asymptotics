import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalDiagramScalars

/-! Inverse-transpose and the literal signed diagram/field twist on
natural matrix units. The covariance identity relates actual matrix
conjugators; it makes no assertion about fixed-point or derived groups. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

def inverseTransposeUnit (u : (Mat R r)ˣ) : (Mat R r)ˣ where
  val := (↑(u⁻¹) : Mat R r).transpose
  inv := (u : Mat R r).transpose
  val_inv := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  inv_val := by
    rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

def inverseTransposeHom : (Mat R r)ˣ →* (Mat R r)ˣ where
  toFun := inverseTransposeUnit R r
  map_one' := by
    apply Units.ext
    change (↑((1 : (Mat R r)ˣ)⁻¹) : Mat R r).transpose = 1
    simp only [inv_one, Units.val_one, Matrix.transpose_one]
  map_mul' u v := by
    apply Units.ext
    change (↑((u * v)⁻¹) : Mat R r).transpose =
      (↑(u⁻¹) : Mat R r).transpose * (↑(v⁻¹) : Mat R r).transpose
    simp only [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

def diagramUnitHom : (Mat R r)ˣ →* (Mat R r)ˣ :=
  (MulAut.conj (signedReversalUnit R r)).toMonoidHom.comp (inverseTransposeHom R r)

def diagramFieldUnitHom (f : R →+* R) : (Mat R r)ˣ →* (Mat R r)ˣ :=
  (diagramUnitHom R r).comp (Units.map f.mapMatrix.toMonoidHom)

theorem diagramFieldUnitHom_val (f : R →+* R) (u : (Mat R r)ˣ) :
    (diagramFieldUnitHom R r f u : Mat R r) =
      (signedReversalUnit R r : Mat R r) *
        (f.mapMatrix (↑(u⁻¹) : Mat R r)).transpose *
          (↑((signedReversalUnit R r)⁻¹) : Mat R r) := rfl

theorem diagramFieldUnitHom_inv_val (f : R →+* R) (u : (Mat R r)ˣ) :
    (↑((diagramFieldUnitHom R r f u)⁻¹) : Mat R r) =
      (signedReversalUnit R r : Mat R r) *
        (f.mapMatrix (u : Mat R r)).transpose *
          (↑((signedReversalUnit R r)⁻¹) : Mat R r) := by
  rw [← map_inv, diagramFieldUnitHom_val, inv_inv]

theorem diagramField_conjugation (f : R →+* R) (u : (Mat R r)ˣ) (X : Mat R r) :
    matrixDiagram R r
        (f.mapMatrix ((u : Mat R r) * X * (↑(u⁻¹) : Mat R r))) =
      (diagramFieldUnitHom R r f u : Mat R r) *
        matrixDiagram R r (f.mapMatrix X) *
          (↑((diagramFieldUnitHom R r f u)⁻¹) : Mat R r) := by
  rw [diagramFieldUnitHom_val, diagramFieldUnitHom_inv_val]
  change (signedReversalUnit R r : Mat R r) *
      (-(f.mapMatrix ((u : Mat R r) * X * (↑(u⁻¹) : Mat R r))).transpose) *
        (↑((signedReversalUnit R r)⁻¹) : Mat R r) =
    ((signedReversalUnit R r : Mat R r) *
        (f.mapMatrix (↑(u⁻¹) : Mat R r)).transpose *
          (↑((signedReversalUnit R r)⁻¹) : Mat R r)) *
      ((signedReversalUnit R r : Mat R r) * (-(f.mapMatrix X).transpose) *
          (↑((signedReversalUnit R r)⁻¹) : Mat R r)) *
        ((signedReversalUnit R r : Mat R r) *
          (f.mapMatrix (u : Mat R r)).transpose *
            (↑((signedReversalUnit R r)⁻¹) : Mat R r))
  simp only [map_mul, Matrix.transpose_mul, mul_neg, neg_mul,
    mul_assoc, Units.inv_mul_cancel_left]

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
