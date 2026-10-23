import SymmetricSubgroupAsymptotics.CFSGGTwoLongTorusAction
import Mathlib.Tactic.FieldSimp

/-! The two actual rank-one torus words in the faithful native G2 group.
Their diagonal actions and the injectivity of their product hold over
every field, without a simplicity assumption on an ordinary G2 model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoNaturalRankTwoTorus
open CFSGGTwoSerreMatrices
variable (K : Type) [Field K]

private theorem vec4_two {R : Type*} (a b c d : R) :
    (![a,b,c,d] : Fin 4 → R) 2 = c := rfl
private theorem vec4_three {R : Type*} (a b c d : R) :
    (![a,b,c,d] : Fin 4 → R) 3 = d := rfl

def shortWeylParameter (t : Kˣ) : naturalGroup K :=
  naturalRoot K false 0 (t : K) * naturalRoot K true 0 (-(t⁻¹ : Kˣ) : K) *
    naturalRoot K false 0 (t : K)

def shortTorus (t : Kˣ) : naturalGroup K :=
  shortWeylParameter K t * shortWeylParameter K (-1)

def shortWeylAction (t : Kˣ) (v : Index → K) : Index → K :=
  Sum.elim
    ![(t : K)*v (pos 1), -(t⁻¹ : Kˣ)*v (pos 0),
      -(t : K)^2*v (neg 2), -v (neg 3)]
    ![(t⁻¹ : Kˣ)*v (neg 1), -(t : K)*v (neg 0),
      -(t⁻¹ : Kˣ)^2*v (pos 2), -v (pos 3)]

def shortTorusAction (t : Kˣ) (v : Index → K) : Index → K :=
  Sum.elim
    ![(t : K)*v (pos 0), (t⁻¹ : Kˣ)*v (pos 1), (t : K)^2*v (pos 2), v (pos 3)]
    ![(t⁻¹ : Kˣ)*v (neg 0), (t : K)*v (neg 1), (t⁻¹ : Kˣ)^2*v (neg 2), v (neg 3)]

private theorem naturalRoot_val (s : Bool) (i : Fin 2) (a : K) :
    ((naturalRoot K s i a).val : Mat K) = (rootTransvection K s i a : Mat K) := rfl

theorem shortWeylParameter_apply (t : Kˣ) (v : Index → K) :
    ((shortWeylParameter K t).val : Mat K) *ᵥ v = shortWeylAction K t v := by
  simp only [shortWeylParameter, Subgroup.coe_mul, Units.val_mul,
    naturalRoot_val, ← Matrix.mulVec_mulVec]
  rw [CFSGGTwoShortRootVectorActions.positive_apply,
    CFSGGTwoShortRootVectorActions.negative_apply,
    CFSGGTwoShortRootVectorActions.positive_apply]
  funext x
  rcases x with i | i <;> fin_cases i <;>
    simp [shortWeylAction, CFSGGTwoShortRootVectorActions.positiveAction,
      CFSGGTwoShortRootVectorActions.negativeAction, pos, neg,
      vec4_two, vec4_three, Units.val_inv_eq_inv_val] <;> field_simp <;> ring

theorem shortTorus_apply (t : Kˣ) (v : Index → K) :
    ((shortTorus K t).val : Mat K) *ᵥ v = shortTorusAction K t v := by
  simp only [shortTorus, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
  rw [shortWeylParameter_apply, shortWeylParameter_apply]
  funext x
  rcases x with i | i <;> fin_cases i <;>
    simp [shortWeylAction, shortTorusAction, pos, neg, vec4_two, vec4_three,
      Units.val_inv_eq_inv_val]

def torusPair (t : Kˣ × Kˣ) : naturalGroup K :=
  shortTorus K t.1 * CFSGGTwoLongTorusAction.longTorus t.2

def pairAction (t : Kˣ × Kˣ) (v : Index → K) : Index → K :=
  Sum.elim
    ![(t.1 : K)*v (pos 0), ((t.1⁻¹ : Kˣ) : K)*(t.2 : K)*v (pos 1),
      (t.1 : K)^2*((t.2⁻¹ : Kˣ) : K)*v (pos 2), v (pos 3)]
    ![((t.1⁻¹ : Kˣ) : K)*v (neg 0), (t.1 : K)*((t.2⁻¹ : Kˣ) : K)*v (neg 1),
      ((t.1⁻¹ : Kˣ) : K)^2*(t.2 : K)*v (neg 2), v (neg 3)]

theorem torusPair_apply (t : Kˣ × Kˣ) (v : Index → K) :
    ((torusPair K t).val : Mat K) *ᵥ v = pairAction K t v := by
  simp only [torusPair, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
  rw [shortTorus_apply, CFSGGTwoLongTorusAction.longTorus_apply]
  funext x
  rcases x with i | i <;> fin_cases i <;>
    simp [shortTorusAction, CFSGGTwoLongTorusAction.torusAction, pairAction,
      pos, neg, vec4_two, vec4_three, mul_assoc]

theorem torusPair_injective : Function.Injective (torusPair K) := by
  intro t u he
  have h (i : Index) := congrArg (fun g : naturalGroup K =>
    (((g.val : Mat K) *ᵥ Pi.single i 1) i)) he
  have h0 : (t.1 : K) = (u.1 : K) := by
    have hh := h (pos 0)
    dsimp only at hh
    rw [torusPair_apply, torusPair_apply] at hh
    simpa [pairAction, pos] using hh
  have ht : t.1 = u.1 := Units.ext h0
  have h1 : ((t.1⁻¹ : Kˣ) : K)*(t.2 : K) = ((u.1⁻¹ : Kˣ) : K)*(u.2 : K) := by
    have hh := h (pos 1)
    dsimp only at hh
    rw [torusPair_apply, torusPair_apply] at hh
    simpa [pairAction, pos] using hh
  rw [ht] at h1
  have hu : (t.2 : K) = (u.2 : K) := mul_left_cancel₀ (Units.ne_zero _) h1
  exact Prod.ext ht (Units.ext hu)

def torusHom : (Kˣ × Kˣ) →* naturalGroup K where
  toFun := torusPair K
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    apply Matrix.ext_of_mulVec_single
    intro i
    change ((torusPair K (1, 1)).val : Mat K) *ᵥ Pi.single i 1 =
      (1 : Mat K) *ᵥ Pi.single i 1
    rw [torusPair_apply, Matrix.one_mulVec]
    funext j
    rcases j with j | j <;> fin_cases j <;>
      simp [pairAction, pos, neg, vec4_two, vec4_three]
  map_mul' t u := by
    apply Subtype.ext
    apply Units.ext
    apply Matrix.ext_of_mulVec_single
    intro i
    change ((torusPair K (t * u)).val : Mat K) *ᵥ Pi.single i 1 =
      (((torusPair K t).val : Mat K) * ((torusPair K u).val : Mat K)) *ᵥ Pi.single i 1
    rw [← Matrix.mulVec_mulVec, torusPair_apply, torusPair_apply, torusPair_apply]
    funext j
    rcases j with j | j <;> fin_cases j <;>
      simp [pairAction, pos, neg, vec4_two, vec4_three, mul_inv_rev,
        mul_pow, mul_assoc, mul_left_comm, mul_comm]

theorem torusHom_injective : Function.Injective (torusHom K) := torusPair_injective K

theorem short_long_commute (a b : Kˣ) :
    Commute (shortTorus K a) (CFSGGTwoLongTorusAction.longTorus b) := by
  change shortTorus K a * CFSGGTwoLongTorusAction.longTorus b =
    CFSGGTwoLongTorusAction.longTorus b * shortTorus K a
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro i
  simp only [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
  rw [shortTorus_apply, CFSGGTwoLongTorusAction.longTorus_apply,
    CFSGGTwoLongTorusAction.longTorus_apply, shortTorus_apply]
  funext j
  rcases j with j | j <;> fin_cases j <;>
    simp [shortTorusAction, CFSGGTwoLongTorusAction.torusAction, pos, neg,
      vec4_two, vec4_three, mul_assoc, mul_left_comm, mul_comm]

end SymmetricSubgroupAsymptotics.CFSGGTwoNaturalRankTwoTorus
