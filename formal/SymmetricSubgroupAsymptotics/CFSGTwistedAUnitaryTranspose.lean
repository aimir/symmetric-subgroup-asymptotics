import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalMiddle

/-! Actual inverse-transpose symmetry of the defining-fixed natural
subgroup. This constructs the opposite action without assuming that a
particular signed reversal belongs to the elementary group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGSerreOrdinaryTwists

theorem inverseTranspose_involutive (K : Type) [Field K] (r : ℕ)
    (u : (Mat K r)ˣ) :
    inverseTransposeHom K r (inverseTransposeHom K r u) = u := by
  apply Units.ext
  change (u : Mat K r).transpose.transpose = (u : Mat K r)
  exact Matrix.transpose_transpose _

theorem inverseTranspose_field_commutes (K : Type) [Field K] (r : ℕ)
    (f : K →+* K) (u : (Mat K r)ˣ) :
    inverseTransposeHom K r (Units.map f.mapMatrix.toMonoidHom u) =
      Units.map f.mapMatrix.toMonoidHom (inverseTransposeHom K r u) := by
  apply Units.ext
  ext i j
  rfl

theorem inverseTranspose_signedReversal (K : Type) [Field K] (r : ℕ) :
    inverseTransposeHom K r (signedReversalUnit K r) = signedReversalUnit K r := by
  apply Units.ext
  change (↑((signedReversalUnit K r)⁻¹) : Mat K r).transpose = _
  rw [signedReversalUnit_inv_eq_transpose, Matrix.transpose_transpose]

theorem inverseTranspose_diagramField_commutes (K : Type) [Field K] (r : ℕ)
    (f : K →+* K) (u : (Mat K r)ˣ) :
    inverseTransposeHom K r (diagramFieldUnitHom K r f u) =
      diagramFieldUnitHom K r f (inverseTransposeHom K r u) := by
  change inverseTransposeHom K r (signedReversalUnit K r *
      inverseTransposeHom K r (Units.map f.mapMatrix.toMonoidHom u) *
        (signedReversalUnit K r)⁻¹) =
    signedReversalUnit K r * inverseTransposeHom K r
      (Units.map f.mapMatrix.toMonoidHom (inverseTransposeHom K r u)) *
        (signedReversalUnit K r)⁻¹
  simp only [map_mul, map_inv, inverseTranspose_signedReversal, inverseTranspose_involutive]
  rw [← inverseTranspose_field_commutes, inverseTranspose_involutive]

def naturalInverseTransposeHom (K : Type) [Field K] (r : ℕ) :
    NaturalElementary K r →* NaturalElementary K r where
  toFun u := ⟨inverseTransposeHom K r u.val, unit_mem_natural_of_det K r _ (by
    change (↑(u.val⁻¹) : Mat K r).transpose.det = 1
    rw [Matrix.det_transpose]
    exact naturalElementary_det K r u⁻¹)⟩
  map_one' := Subtype.ext (map_one (inverseTransposeHom K r))
  map_mul' u v := Subtype.ext (map_mul (inverseTransposeHom K r) u.val v.val)

theorem naturalInverseTranspose_fixed (q : CFSG.PrimePower) (r : ℕ)
    (u : naturalFixed r q) : naturalInverseTransposeHom (q.Extension 2) r u.val ∈ naturalFixed r q := by
  have h := congrArg (inverseTransposeHom (q.Extension 2) r) u.property
  change inverseTransposeHom (q.Extension 2) r
    (diagramFieldUnitHom (q.Extension 2) r (definingFieldAutomorphism q 2).toRingHom u.val.val) =
      inverseTransposeHom (q.Extension 2) r u.val.val at h
  rw [inverseTranspose_diagramField_commutes] at h
  exact h

def fixedInverseTransposeHom (q : CFSG.PrimePower) (r : ℕ) : naturalFixed r q →* naturalFixed r q where
  toFun u := ⟨naturalInverseTransposeHom (q.Extension 2) r u.val, naturalInverseTranspose_fixed q r u⟩
  map_one' := Subtype.ext (map_one (naturalInverseTransposeHom (q.Extension 2) r))
  map_mul' u v := Subtype.ext (map_mul (naturalInverseTransposeHom (q.Extension 2) r) u.val v.val)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
