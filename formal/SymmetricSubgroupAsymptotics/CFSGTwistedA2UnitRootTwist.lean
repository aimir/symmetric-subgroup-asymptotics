import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalUnitTwist
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalReversal
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalRealization
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalFieldTwist

/-! Literal signed diagram--field transport of natural simple-root units.
This is a symbolic unit identity, before any fixed subgroup recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnitRootTwist
open CFSGTwistedANaturalMatrices
variable (K : Type) [Field K] (σ : K ≃+* K) (r : ℕ)

theorem map_rootMatrix (neg : Bool) (i : Fin r) :
    σ.toRingHom.mapMatrix (rootMatrix K r neg i) = rootMatrix K r neg i := by
  cases neg
  · exact map_positive K r σ.toRingHom i
  · exact map_negative K r σ.toRingHom i

theorem diagram_rootMatrix (neg : Bool) (i : Fin r) :
    matrixDiagram K r (rootMatrix K r neg i) = rootMatrix K r neg i.rev := by
  cases neg
  · exact matrixDiagram_positive K r i
  · exact matrixDiagram_negative K r i

theorem simpleUnit_twist (neg : Bool) (i : Fin r) (a : K) :
    diagramFieldUnitHom K r σ.toRingHom (naturalRootUnit K r neg i a) =
      naturalRootUnit K r neg i.rev (σ a) := by
  let J := signedReversalUnit K r
  have hh := diagram_rootMatrix K r neg i
  change (J : Mat K r) * (-(rootMatrix K r neg i).transpose) *
    (↑(J⁻¹) : Mat K r) = rootMatrix K r neg i.rev at hh
  have hconj := congrArg Neg.neg hh
  simp only [mul_neg, neg_mul, neg_neg] at hconj
  apply Units.ext
  rw [diagramFieldUnitHom_val, naturalRootUnit_inv_val, realizationData_fieldRoot]
  change (J : Mat K r) *
    (σ.toRingHom.mapMatrix (1 - a • rootMatrix K r neg i)).transpose *
      (↑(J⁻¹) : Mat K r) = 1 + σ a • rootMatrix K r neg i.rev
  rw [map_sub, map_one, map_matrix_smul, map_rootMatrix]
  simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
    mul_sub, sub_mul, mul_one, Units.mul_inv, mul_smul_comm, smul_mul_assoc]
  rw [hconj, smul_neg, sub_neg_eq_add]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnitRootTwist
