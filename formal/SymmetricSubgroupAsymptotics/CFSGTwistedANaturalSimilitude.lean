import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalUnitTwist
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalImageKernel
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalReversal

/-! An elementary natural lift whose conjugation commutes with the
original diagram/field equation is a genuine similitude of the literal
signed form. The multiplier is proved to exist and to be nonzero; no
unitary realization or scalar-normalization hypothesis is supplied. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
open CFSG.Models.Chevalley

theorem conjugation_ratio_commutes {R : Type*} [Monoid R] (u v : Rˣ) (X : R)
    (h : (u : R) * X * (↑(u⁻¹) : R) = (v : R) * X * (↑(v⁻¹) : R)) :
    (↑(v⁻¹ * u) : R) * X = X * (↑(v⁻¹ * u) : R) := by
  apply (CFSGUnitConjugation.fix_iff_commute (v⁻¹ * u) X).mp
  have hh := congrArg (fun Z : R => (↑(v⁻¹) : R) * Z * (v : R)) h
  simpa only [_root_.mul_inv_rev, inv_inv, Units.val_mul,
    mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, one_mul, mul_one] using hh

theorem natural_twist_equivariant_lift_similitude
    (K : Type) [Field K] (r : ℕ) (hr : 1 ≤ r) (f : K →+* K)
    (u : (Mat K r)ˣ)
    (hfix : ∀ x : Space (CartanMatrix.A r) K,
      matrixDiagram K r (f.mapMatrix
        ((u : Mat K r) * CFSGSerreSquareZeroMatrix.baseChange (realizationData r) K x *
          (↑(u⁻¹) : Mat K r))) =
        (u : Mat K r) *
          matrixDiagram K r
            (f.mapMatrix (CFSGSerreSquareZeroMatrix.baseChange (realizationData r) K x)) *
          (↑(u⁻¹) : Mat K r)) :
    ∃ c : K, c ≠ 0 ∧
      (f.mapMatrix (u : Mat K r)).transpose *
        (↑((signedReversalUnit K r)⁻¹) : Mat K r) * (u : Mat K r) =
          c • (↑((signedReversalUnit K r)⁻¹) : Mat K r) := by
  let v := diagramFieldUnitHom K r f u
  have hroot (neg : Bool) (i : Fin r) :
      (↑(v⁻¹ * u) : Mat K r) * rootMatrix K r neg i =
        rootMatrix K r neg i * (↑(v⁻¹ * u) : Mat K r) := by
    have he : (u : Mat K r) * rootMatrix K r neg i * (↑(u⁻¹) : Mat K r) =
        (v : Mat K r) * rootMatrix K r neg i * (↑(v⁻¹) : Mat K r) := by
      cases neg
      · have h := hfix (1 ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator (CartanMatrix.A r)
          (CartanMatrix.Generators.E i.rev))
        rw [diagramField_conjugation] at h
        simpa only [naturalBaseChange_E, map_positive, matrixDiagram_positive,
          Fin.rev_rev, rootMatrix, Bool.false_eq_true, if_false] using h.symm
      · have h := hfix (1 ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator (CartanMatrix.A r)
          (CartanMatrix.Generators.F i.rev))
        rw [diagramField_conjugation] at h
        simpa only [naturalBaseChange_F, map_negative, matrixDiagram_negative,
          Fin.rev_rev, rootMatrix, if_true] using h.symm
    exact conjugation_ratio_commutes u v _ he
  obtain ⟨c, hc⟩ := natural_commutant_scalar K r hr
    (↑(v⁻¹ * u) : Mat K r) hroot
  have hcn : c ≠ 0 := by
    intro hzero
    have hn := Units.ne_zero (v⁻¹ * u)
    apply hn
    simpa only [hzero, zero_smul] using hc
  refine ⟨c, hcn, ?_⟩
  have hh := congrArg
    (fun X : Mat K r => (↑((signedReversalUnit K r)⁻¹) : Mat K r) * X) hc
  change (↑((signedReversalUnit K r)⁻¹) : Mat K r) *
    ((↑(v⁻¹) : Mat K r) * (u : Mat K r)) =
      (↑((signedReversalUnit K r)⁻¹) : Mat K r) * (c • (1 : Mat K r)) at hh
  dsimp only [v] at hh
  rw [diagramFieldUnitHom_inv_val] at hh
  simpa only [mul_assoc, Units.inv_mul_cancel_left, mul_smul_comm, mul_one] using hh

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
