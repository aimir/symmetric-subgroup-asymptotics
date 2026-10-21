import SymmetricSubgroupAsymptotics.CFSGSuzukiTorusElements
import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentLaw
import SymmetricSubgroupAsymptotics.CFSGSuzukiFieldParameterMaps
import Mathlib.Tactic.FieldSimp

/-! A normalized parameter chart for the original Suzuki diagonal torus,
and its exact action on original unipotent parameters. Every normalized
torus element is explicitly an original torus element. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical CharTwo
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiTorus
open CFSGSuzukiFieldParameters CFSGSuzukiUnipotent

variable {K : Type*} [Field K]

def diagonalTorus (t : K →+* K) (c : K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.diagonal ![c,t c/c,c/t c,c⁻¹]

theorem original_torus_eq_diagonalTorus (m : ℕ)
    (c : (CFSG.Models.SuzukiConstruction.Field m)ˣ) :
    CFSG.Models.SuzukiConstruction.torus m c=
      diagonalTorus (theta m) (torusParameter m (c : Field m)) := by
  have hx : (c : Field m)≠0 := Units.ne_zero c
  have hy : inverseTheta m (c : Field m)≠0 := by
    intro he
    apply hx
    apply (inverseTheta m).injective
    simpa only [map_zero] using he
  have hθ : theta m (torusParameter m (c : Field m))=
      (inverseTheta m (c : Field m))^2*(c : Field m) := by
    rw [torusParameter,map_mul,theta_inverseTheta,←inverseTheta_square]
  simp only [CFSG.Models.SuzukiConstruction.torus,diagonalTorus]
  congr 1
  funext i
  fin_cases i
  · change (c : Field m)^(1+2^m)=torusParameter m (c : Field m)
    exact (torusParameter_eq_pow m (c : Field m)).symm
  · change (c : Field m)^(2^m)=
      theta m (torusParameter m (c : Field m))/torusParameter m (c : Field m)
    rw [hθ,torusParameter,←inverseTheta_apply]
    field_simp [hx,hy] <;> ring
  · change ((c⁻¹ : (Field m)ˣ) : Field m)^(2^m)=
      torusParameter m (c : Field m)/theta m (torusParameter m (c : Field m))
    rw [Units.val_inv_eq_inv_val,inv_pow,←inverseTheta_apply,hθ,torusParameter]
    field_simp [hx,hy] <;> ring
  · change ((c⁻¹ : (Field m)ˣ) : Field m)^(1+2^m)=
      (torusParameter m (c : Field m))⁻¹
    rw [Units.val_inv_eq_inv_val,inv_pow,torusParameter_eq_pow]

/-- The original torus parameter is retained explicitly through the
proved inverse scalar chart. -/
def normalizedTorusElement (m : ℕ) (c : (Field m)ˣ) : CFSGSuzukiTorus.Ambient m :=
  torusElement m (Units.mk0 (inverseTorusParameter m (c : Field m))
    (div_ne_zero (pow_ne_zero 2 (Units.ne_zero c)) (theta_ne_zero m (Units.ne_zero c))))

@[simp] theorem normalizedTorusElement_coe (m : ℕ) (c : (Field m)ˣ) :
    (normalizedTorusElement m c : CFSG.Models.SuzukiConstruction.Mat m)=
      diagonalTorus (theta m) (c : Field m) := by
  rw [normalizedTorusElement,torusElement_coe,original_torus_eq_diagonalTorus]
  change diagonalTorus (theta m) (torusParameter m (inverseTorusParameter m (c : Field m)))=_
  rw [torusParameter_inverseTorusParameter]

theorem normalizedTorusElement_mem_model (m : ℕ) (c : (Field m)ˣ) :
    normalizedTorusElement m c∈CFSG.Models.SuzukiConstruction.subgroup m :=
  torusElement_mem_model m _

variable [CharP K 2]

/-- Exact normalized diagonal scaling, before making any group-order or
Bruhat assertion. -/
theorem diagonalTorus_mul_unipotent (t : K →+* K) (ht : ∀ x,t (t x)=x^2)
    (c a b : K) (hc : c≠0) :
    diagonalTorus t c*twistedArray t a b=
      twistedArray t (t c*a/c^2) (b/t c)*diagonalTorus t c := by
  have htc : t c≠0 := by
    intro he
    apply hc
    apply t.injective
    simpa only [map_zero] using he
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalTorus,twistedArray,Matrix.diagonal_mul,Matrix.mul_diagonal,
      map_mul,map_div₀,map_pow,ht] <;>
    field_simp [hc,htc] <;> ring_nf <;> simp

theorem normalizedTorus_conjugation (m : ℕ) (c : (Field m)ˣ) (a b : Field m) :
    normalizedTorusElement m c*unipotentElement m a b*(normalizedTorusElement m c)⁻¹=
      unipotentElement m (theta m (c : Field m)*a/(c : Field m)^2) (b/theta m (c : Field m)) := by
  have hm : normalizedTorusElement m c*unipotentElement m a b=
      unipotentElement m (theta m (c : Field m)*a/(c : Field m)^2)
        (b/theta m (c : Field m))*normalizedTorusElement m c := by
    apply Units.ext
    change (normalizedTorusElement m c : CFSG.Models.SuzukiConstruction.Mat m)*
        CFSG.Models.SuzukiConstruction.unipotent m a b=
      CFSG.Models.SuzukiConstruction.unipotent m
        (theta m (c : Field m)*a/(c : Field m)^2) (b/theta m (c : Field m))*
        (normalizedTorusElement m c : CFSG.Models.SuzukiConstruction.Mat m)
    rw [normalizedTorusElement_coe,unipotent_eq_twistedArray,unipotent_eq_twistedArray]
    exact diagonalTorus_mul_unipotent (theta m) (theta_twice m) _ a b (Units.ne_zero c)
  have hh := congrArg (fun X : CFSGSuzukiTorus.Ambient m => X*(normalizedTorusElement m c)⁻¹) hm
  simpa only [mul_assoc,mul_inv_cancel,mul_one] using hh

end SymmetricSubgroupAsymptotics.CFSGSuzukiTorus
