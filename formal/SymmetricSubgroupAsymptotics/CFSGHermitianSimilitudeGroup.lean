import SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonality
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-! Actual linear isometries and similitudes of an invertible signed
Hermitian matrix. Their unique multiplier belongs to the literal fixed
unit group; its unit fibre is the actual isometry group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianSimilitudeGroup
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
abbrev LinearGroup := (I → K) ≃ₗ[K] (I → K)

def isometries (sigma : K ≃+* K) (H : (Matrix I I K)ˣ) :
    Subgroup (LinearGroup (K := K) (I := I)) where
  carrier := {e | ∀ v w, hermitianPair sigma H (e v) (e w) = hermitianPair sigma H v w}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro e f he hf v w
    exact (he (f v) (f w)).trans (hf v w)
  inv_mem' := by
    intro e he v w
    have h := he (e.symm v) (e.symm w)
    simpa only [LinearEquiv.apply_symm_apply] using h.symm

def similitudes (sigma : K ≃+* K) (H : (Matrix I I K)ˣ) :
    Subgroup (LinearGroup (K := K) (I := I)) where
  carrier := {e | ∃ c : K, c ≠ 0 ∧ ∀ v w,
    hermitianPair sigma H (e v) (e w) = c * hermitianPair sigma H v w}
  one_mem' := ⟨1, one_ne_zero, fun _ _ => (one_mul _).symm⟩
  mul_mem' := by
    rintro e f ⟨c, hc, he⟩ ⟨d, hd, hf⟩
    refine ⟨c * d, mul_ne_zero hc hd, fun v w => ?_⟩
    change hermitianPair sigma H (e (f v)) (e (f w)) = _
    rw [he, hf, mul_assoc]
  inv_mem' := by
    rintro e ⟨c, hc, he⟩
    refine ⟨c⁻¹, inv_ne_zero hc, fun v w => ?_⟩
    have h := he (e.symm v) (e.symm w)
    simp only [LinearEquiv.apply_symm_apply] at h
    change hermitianPair sigma H (e.symm v) (e.symm w) = _
    rw [h, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem multiplier_unique (sigma : K ≃+* K) (H : (Matrix I I K)ˣ)
    (i₀ : I) (e : LinearGroup (K := K) (I := I)) (c d : K)
    (hc : ∀ v w, hermitianPair sigma H (e v) (e w) = c * hermitianPair sigma H v w)
    (hd : ∀ v w, hermitianPair sigma H (e v) (e w) = d * hermitianPair sigma H v w) : c = d := by
  let v : I → K := Pi.single i₀ 1
  have hv : v ≠ 0 := by
    intro h
    have hh := congrFun h i₀
    simp [v] at hh
  obtain ⟨w, hw⟩ := hermitianPair_surjective sigma H v hv 1
  have hh := (hc v w).symm.trans (hd v w)
  simpa only [hw, mul_one] using hh

def multiplier (sigma : K ≃+* K) (H : (Matrix I I K)ˣ)
    (e : similitudes sigma H) : Kˣ :=
  Units.mk0 (Classical.choose e.property) (Classical.choose_spec e.property).1

theorem multiplier_spec (sigma : K ≃+* K) (H : (Matrix I I K)ˣ)
    (e : similitudes sigma H) (v w : I → K) :
    hermitianPair sigma H (e.val v) (e.val w) =
      (multiplier sigma H e : K) * hermitianPair sigma H v w :=
  (Classical.choose_spec e.property).2 v w

def multiplierHom (sigma : K ≃+* K) (H : (Matrix I I K)ˣ) (i₀ : I) :
    similitudes sigma H →* Kˣ where
  toFun := multiplier sigma H
  map_one' := by
    apply Units.ext
    apply multiplier_unique sigma H i₀ (1 : LinearGroup (K := K) (I := I))
    · exact multiplier_spec sigma H 1
    · intro v w
      exact (one_mul _).symm
  map_mul' e f := by
    apply Units.ext
    apply multiplier_unique sigma H i₀ (e.val * f.val)
    · exact multiplier_spec sigma H (e * f)
    · intro v w
      change hermitianPair sigma H (e.val (f.val v)) (e.val (f.val w)) = _
      rw [multiplier_spec, multiplier_spec, Units.val_mul, mul_assoc]

def fixedUnits (sigma : K ≃+* K) : Subgroup Kˣ where
  carrier := {z | sigma (z : K) = (z : K)}
  one_mem' := map_one sigma
  mul_mem' := by
    intro z w hz hw
    change sigma ((z : K) * (w : K)) = (z : K) * (w : K)
    rw [map_mul, hz, hw]
  inv_mem' := by
    intro z hz
    change sigma ((z⁻¹ : Kˣ) : K) = ((z⁻¹ : Kˣ) : K)
    rw [Units.val_inv_eq_inv_val, map_inv₀, hz]

def fixedMultiplierHom (sigma : K ≃+* K) (hsigma : ∀ x, sigma (sigma x) = x)
    (eps : K) (H : (Matrix I I K)ˣ)
    (hH : (H : Matrix I I K).map sigma = eps • (H : Matrix I I K).transpose)
    (i₀ : I) : similitudes sigma H →* fixedUnits sigma :=
  (multiplierHom sigma H i₀).codRestrict (fixedUnits sigma) (fun e => by
    change sigma (multiplier sigma H e : K) = (multiplier sigma H e : K)
    exact CFSGHermitianOrthogonality.multiplier_fixed sigma (RingEquiv.refl K)
      hsigma eps rfl H hH e.val (multiplier sigma H e)
      (fun v w => multiplier_spec sigma H e v w) i₀)

end SymmetricSubgroupAsymptotics.CFSGHermitianSimilitudeGroup
