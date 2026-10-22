import SymmetricSubgroupAsymptotics.CFSGTwistedADerivedIsometricLift

/-! The actual signed diagram/field fixed-unit equation is equivalent
to its literal signed-form isometry equation. This is an equality of
conditions on individual natural matrix units, not model recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
variable (K : Type) [Field K] (r : ℕ) (f : K →+* K)

theorem unit_fixed_of_isometric (u : (Mat K r)ˣ)
    (hu : (f.mapMatrix (u : Mat K r)).transpose *
        (↑((signedReversalUnit K r)⁻¹) : Mat K r) * (u : Mat K r) =
      (↑((signedReversalUnit K r)⁻¹) : Mat K r)) :
    diagramFieldUnitHom K r f u = u := by
  have hh : (diagramFieldUnitHom K r f u)⁻¹ * u = 1 := by
    apply Units.ext
    change (↑((diagramFieldUnitHom K r f u)⁻¹) : Mat K r) * (u : Mat K r) = 1
    rw [diagramFieldUnitHom_inv_val]
    calc
      _ = (signedReversalUnit K r : Mat K r) *
          ((f.mapMatrix (u : Mat K r)).transpose *
            (↑((signedReversalUnit K r)⁻¹) : Mat K r) * (u : Mat K r)) := by
        simp only [mul_assoc]
      _ = (signedReversalUnit K r : Mat K r) *
          (↑((signedReversalUnit K r)⁻¹) : Mat K r) := congrArg
        (fun A : Mat K r => (signedReversalUnit K r : Mat K r) * A) hu
      _ = 1 := Units.mul_inv (signedReversalUnit K r)
  exact inv_mul_eq_one.mp hh

theorem unit_fixed_iff_isometric (u : (Mat K r)ˣ) :
    diagramFieldUnitHom K r f u = u ↔
      (f.mapMatrix (u : Mat K r)).transpose *
        (↑((signedReversalUnit K r)⁻¹) : Mat K r) * (u : Mat K r) =
          (↑((signedReversalUnit K r)⁻¹) : Mat K r) :=
  ⟨fixed_unit_isometric K r f u, unit_fixed_of_isometric K r f u⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
