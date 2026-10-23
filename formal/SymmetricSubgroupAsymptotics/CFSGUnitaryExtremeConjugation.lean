import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralLineAction

/-! Same-line conjugation of extreme roots, at the raw matrix level.
The relative conjugator's actual signed-form equation is the only form
input. This separates matrix algebra from deep original-source types. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices

theorem extreme_conjugate_of_span_eq {K : Type} [Field K] (r : ℕ)
    (sigma : K ≃+* K) (g h : (Mat K r)ˣ)
    (hform : ((((h⁻¹ * g : (Mat K r)ˣ) : Mat K r).map sigma).transpose *
      (signedReversalUnit K r : Mat K r) * ((h⁻¹ * g : (Mat K r)ˣ) : Mat K r)) =
      (signedReversalUnit K r : Mat K r))
    (hp : K ∙ ((g : Mat K r) *ᵥ (Pi.single (0 : Fin (r + 1)) 1)) =
      K ∙ ((h : Mat K r) *ᵥ (Pi.single (0 : Fin (r + 1)) 1))) (b : K) :
    ∃ a : K,
      (g : Mat K r) * (1 + Matrix.single (0 : Fin (r + 1)) (Fin.last r) b) *
          ((g⁻¹ : (Mat K r)ˣ) : Mat K r) =
        (h : Mat K r) * (1 + Matrix.single (0 : Fin (r + 1)) (Fin.last r)
          (a * sigma a * b)) * ((h⁻¹ : (Mat K r)ˣ) : Mat K r) := by
  let e : Fin (r + 1) → K := Pi.single 0 1
  have hv : (g : Mat K r) *ᵥ e ∈ K ∙ ((h : Mat K r) *ᵥ e) := by
    rw [← hp]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
  let k := h⁻¹ * g
  have haxis : (k : Mat K r) *ᵥ e = a • e := by
    change (((h⁻¹ : (Mat K r)ˣ) : Mat K r) * (g : Mat K r)) *ᵥ e = a • e
    rw [← Matrix.mulVec_mulVec, ← ha, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Units.inv_mul, Matrix.one_mulVec]
  have hcol (i : Fin (r + 1)) : (k : Mat K r) i 0 = if i = 0 then a else 0 := by
    have hi := congrFun haxis i
    simpa only [e, Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply,
      Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, eq_comm] using hi
  have hk := extreme_single_conjugation r sigma k a b hform hcol
  have hki : ((k⁻¹ : (Mat K r)ˣ) : Mat K r) =
      ((g⁻¹ : (Mat K r)ˣ) : Mat K r) * (h : Mat K r) := by
    change (((h⁻¹ * g)⁻¹ : (Mat K r)ˣ) : Mat K r) = _
    rw [mul_inv_rev, inv_inv]
    rfl
  refine ⟨a, ?_⟩
  calc
    _ = ((h : Mat K r) * ((h⁻¹ : (Mat K r)ˣ) : Mat K r)) * (g : Mat K r) *
        (1 + Matrix.single (0 : Fin (r + 1)) (Fin.last r) b) *
        ((g⁻¹ : (Mat K r)ˣ) : Mat K r) *
        ((h : Mat K r) * ((h⁻¹ : (Mat K r)ˣ) : Mat K r)) := by
      rw [Units.mul_inv, one_mul, mul_one]
    _ = (h : Mat K r) * ((k : Mat K r) *
        (1 + Matrix.single (0 : Fin (r + 1)) (Fin.last r) b) *
        ((k⁻¹ : (Mat K r)ˣ) : Mat K r)) * ((h⁻¹ : (Mat K r)ˣ) : Mat K r) := by
      rw [hki]
      change _ = (h : Mat K r) *
        ((((h⁻¹ : (Mat K r)ˣ) : Mat K r) * (g : Mat K r)) *
        (1 + Matrix.single (0 : Fin (r + 1)) (Fin.last r) b) *
        (((g⁻¹ : (Mat K r)ˣ) : Mat K r) * (h : Mat K r))) *
        ((h⁻¹ : (Mat K r)ˣ) : Mat K r)
      simp only [mul_assoc]
    _ = _ := congrArg (fun M : Mat K r =>
      (h : Mat K r) * M * ((h⁻¹ : (Mat K r)ˣ) : Mat K r)) hk

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
