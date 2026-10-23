import SymmetricSubgroupAsymptotics.CFSGGTwoNaturalRankTwoTorus
import SymmetricSubgroupAsymptotics.CFSGGTwoPositiveWordActions

/-! The actual rank-two torus conjugates every literal positive root by
its root character, in every field. Sparse vector actions establish the
identity before transport to the original Model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoNaturalPositiveTorusAction
open CFSGGTwoSerreMatrices CFSGGTwoNaturalRankTwoTorus
open CFSGGTwoPositiveDirections CFSGGTwoPositiveRootMatrices CFSGGTwoPositiveWordActions
variable (K : Type) [Field K]

private theorem vec4_two {R : Type*} (a b c d : R) :
    (![a,b,c,d] : Fin 4 → R) 2 = c := rfl
private theorem vec4_three {R : Type*} (a b c d : R) :
    (![a,b,c,d] : Fin 4 → R) 3 = d := rfl

def rootScale (t : Kˣ × Kˣ) (j : Fin 6) : Kˣ :=
  match j.val with
  | 0 => t.1^2*t.2⁻¹
  | 1 => (t.1⁻¹)^3*t.2^2
  | 2 => t.1⁻¹*t.2
  | 3 => t.1
  | 4 => t.1^3*t.2⁻¹
  | _ => t.2

private theorem action_covariance_0 (t : Kˣ × Kˣ) (a : K) (v : Index → K) :
    pairAction K t (action0 K a v) =
      action0 K (a*(rootScale K t 0 : K)) (pairAction K t v) := by
  funext x
  rcases x with i | i <;> fin_cases i <;>
    simp [pairAction, action0, rootScale, pos, neg, vec4_two, vec4_three,
      Units.val_inv_eq_inv_val] <;> field_simp <;> ring

private theorem action_covariance_1 (t : Kˣ × Kˣ) (a : K) (v : Index → K) :
    pairAction K t (action1 K a v) =
      action1 K (a*(rootScale K t 1 : K)) (pairAction K t v) := by
  funext x
  rcases x with i | i <;> fin_cases i <;>
    simp [pairAction, action1, rootScale, pos, neg, vec4_two, vec4_three,
      Units.val_inv_eq_inv_val] <;> field_simp <;> ring

private theorem action_covariance_2 (t : Kˣ × Kˣ) (a : K) (v : Index → K) :
    pairAction K t (action2 K a v) =
      action2 K (a*(rootScale K t 2 : K)) (pairAction K t v) := by
  funext x
  rcases x with i | i <;> fin_cases i <;>
    simp [pairAction, action2, rootScale, pos, neg, vec4_two, vec4_three,
      Units.val_inv_eq_inv_val] <;> field_simp <;> ring

private theorem action_covariance_3 (t : Kˣ × Kˣ) (a : K) (v : Index → K) :
    pairAction K t (action3 K a v) =
      action3 K (a*(rootScale K t 3 : K)) (pairAction K t v) := by
  funext x
  rcases x with i | i <;> fin_cases i <;>
    simp [pairAction, action3, rootScale, pos, neg, vec4_two, vec4_three,
      Units.val_inv_eq_inv_val] <;> field_simp <;> ring

private theorem action_covariance_4 (t : Kˣ × Kˣ) (a : K) (v : Index → K) :
    pairAction K t (action4 K a v) =
      action4 K (a*(rootScale K t 4 : K)) (pairAction K t v) := by
  funext x
  rcases x with i | i <;> fin_cases i <;>
    simp [pairAction, action4, rootScale, pos, neg, vec4_two, vec4_three,
      Units.val_inv_eq_inv_val] <;> field_simp <;> ring

private theorem action_covariance_5 (t : Kˣ × Kˣ) (a : K) (v : Index → K) :
    pairAction K t (action5 K a v) =
      action5 K (a*(rootScale K t 5 : K)) (pairAction K t v) := by
  funext x
  rcases x with i | i <;> fin_cases i <;>
    simp [pairAction, action5, rootScale, pos, neg, vec4_two, vec4_three,
      Units.val_inv_eq_inv_val] <;> field_simp <;> ring

theorem positiveAction_covariance (t : Kˣ × Kˣ) (j : Fin 6)
    (a : K) (v : Index → K) :
    pairAction K t (positiveAction K j a v) =
      positiveAction K j (a*(rootScale K t j : K)) (pairAction K t v) := by
  fin_cases j
  · exact action_covariance_0 K t a v
  · exact action_covariance_1 K t a v
  · exact action_covariance_2 K t a v
  · exact action_covariance_3 K t a v
  · exact action_covariance_4 K t a v
  · exact action_covariance_5 K t a v

theorem torusPair_positiveRoot (t : Kˣ × Kˣ) (j : Fin 6) (a : K) :
    torusPair K t * (⟨positiveRoot K j a, positiveRoot_mem K j a⟩ : naturalGroup K) *
      (torusPair K t)⁻¹ =
      ⟨positiveRoot K j (a*(rootScale K t j : K)),
        positiveRoot_mem K j (a*(rootScale K t j : K))⟩ := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro i
  change (((torusPair K t).val : Mat K)*(positiveRoot K j a : Mat K)) *ᵥ Pi.single i 1 =
    ((positiveRoot K j (a*(rootScale K t j : K)) : Mat K)*
      ((torusPair K t).val : Mat K)) *ᵥ Pi.single i 1
  rw [←Matrix.mulVec_mulVec, ←Matrix.mulVec_mulVec, torusPair_apply, torusPair_apply,
    positiveRoot_val, positiveRoot_val, polynomialRoot_apply, polynomialRoot_apply]
  exact positiveAction_covariance K t j a (Pi.single i 1)

end SymmetricSubgroupAsymptotics.CFSGGTwoNaturalPositiveTorusAction
