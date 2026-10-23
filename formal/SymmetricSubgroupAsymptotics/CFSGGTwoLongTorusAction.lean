import SymmetricSubgroupAsymptotics.CFSGGTwoRootParameters
import SymmetricSubgroupAsymptotics.CFSGGTwoShortRootVectorActions
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The actual long-node rank-one torus in the natural G2 group.
Its conjugation on the short simple root has exponent minus one, in
every characteristic. The torus is a literal word in the root groups. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoLongTorusAction
open CFSGGTwoSerreMatrices
variable {K : Type} [Field K]

private theorem vec4_two {R : Type*} (a b c d : R) :
    (![a,b,c,d] : Fin 4 → R) 2 = c := rfl
private theorem vec4_three {R : Type*} (a b c d : R) :
    (![a,b,c,d] : Fin 4 → R) 3 = d := rfl

def positiveAction (t : K) (v : Index → K) : Index → K :=
  Sum.elim ![v (pos 0), v (pos 1)+t*v (pos 2), v (pos 2), v (pos 3)]
    ![v (neg 0), v (neg 1), v (neg 2)-t*v (neg 1), v (neg 3)]

def negativeAction (t : K) (v : Index → K) : Index → K :=
  Sum.elim ![v (pos 0), v (pos 1), v (pos 2)+t*v (pos 1), v (pos 3)]
    ![v (neg 0), v (neg 1)-t*v (neg 2), v (neg 2), v (neg 3)]

theorem positive_apply (t : K) (v : Index → K) :
    (rootTransvection K false 1 t : Mat K) *ᵥ v = positiveAction t v := by
  simp only [rootTransvection_val, rootMatrix, rootSecond, Bool.false_eq_true, if_false,
    positive_one_explicit, positiveSecond, if_neg (by decide : (1 : Fin 2) ≠ 0),
    smul_zero, add_zero, Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  funext x
  rcases x with i | i <;> fin_cases i <;>
    simp [positiveAction, pos, neg,
      Sum.inl_ne_inr, Sum.inr_ne_inl, Fin.ext_iff, vec4_two, vec4_three] <;> ring

theorem negative_apply (t : K) (v : Index → K) :
    (rootTransvection K true 1 t : Mat K) *ᵥ v = negativeAction t v := by
  simp only [rootTransvection_val, rootMatrix, rootSecond, if_true, negative,
    negativeSecond, positive_one_explicit, positiveSecond,
    if_neg (by decide : (1 : Fin 2) ≠ 0), Matrix.transpose_zero,
    smul_zero, add_zero, Matrix.transpose_sub, Matrix.transpose_single,
    Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.single_mulVec]
  funext x
  rcases x with i | i <;> fin_cases i <;>
    simp [negativeAction, pos, neg,
      Sum.inl_ne_inr, Sum.inr_ne_inl, Fin.ext_iff, vec4_two, vec4_three] <;> ring

def longWeylParameter (t : Kˣ) : naturalGroup K :=
  naturalRoot K false 1 (t : K) * naturalRoot K true 1 (-(t⁻¹ : Kˣ) : K) *
    naturalRoot K false 1 (t : K)

def longTorus (t : Kˣ) : naturalGroup K :=
  longWeylParameter t * longWeylParameter (-1)

def torusAction (t : Kˣ) (v : Index → K) : Index → K :=
  Sum.elim ![v (pos 0), (t : K)*v (pos 1), (t⁻¹ : Kˣ)*v (pos 2), v (pos 3)]
    ![v (neg 0), (t⁻¹ : Kˣ)*v (neg 1), (t : K)*v (neg 2), v (neg 3)]

def weylAction (t : Kˣ) (v : Index → K) : Index → K :=
  Sum.elim ![v (pos 0), (t : K)*v (pos 2), -(t⁻¹ : Kˣ)*v (pos 1), v (pos 3)]
    ![v (neg 0), (t⁻¹ : Kˣ)*v (neg 2), -(t : K)*v (neg 1), v (neg 3)]

private theorem naturalRoot_val (s : Bool) (i : Fin 2) (a : K) :
    ((naturalRoot K s i a).val : Mat K) = (rootTransvection K s i a : Mat K) := rfl

theorem longWeylParameter_apply (t : Kˣ) (v : Index → K) :
    ((longWeylParameter t).val : Mat K) *ᵥ v = weylAction t v := by
  simp only [longWeylParameter, Subgroup.coe_mul, Units.val_mul,
    naturalRoot_val, ← Matrix.mulVec_mulVec]
  rw [positive_apply, negative_apply, positive_apply]
  funext x
  rcases x with i | i <;> fin_cases i <;>
    simp [positiveAction, negativeAction, weylAction, pos, neg,
      vec4_two, vec4_three, Units.val_inv_eq_inv_val] <;>
    field_simp <;> ring

theorem longTorus_apply (t : Kˣ) (v : Index → K) :
    ((longTorus t).val : Mat K) *ᵥ v = torusAction t v := by
  simp only [longTorus, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
  rw [longWeylParameter_apply, longWeylParameter_apply]
  funext x
  rcases x with i | i <;> fin_cases i <;>
    simp [weylAction, torusAction, pos, neg, vec4_two, vec4_three,
      Units.val_inv_eq_inv_val]

theorem longTorus_short_root (t : Kˣ) (a : K) :
    longTorus t * naturalRoot K false 0 a * (longTorus t)⁻¹ =
      naturalRoot K false 0 (a*(t⁻¹ : Kˣ)) := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro j
  simp only [Subgroup.coe_mul, Units.val_mul, naturalRoot_val, ← Matrix.mulVec_mulVec]
  rw [longTorus_apply, longTorus_apply]
  rw [CFSGGTwoShortRootVectorActions.positive_apply,
    CFSGGTwoShortRootVectorActions.positive_apply]
  funext x
  rcases x with i | i <;> fin_cases i <;>
    simp [torusAction, CFSGGTwoShortRootVectorActions.positiveAction,
      pos, neg, vec4_two, vec4_three, Units.val_inv_eq_inv_val] <;>
    field_simp <;> ring

end SymmetricSubgroupAsymptotics.CFSGGTwoLongTorusAction
