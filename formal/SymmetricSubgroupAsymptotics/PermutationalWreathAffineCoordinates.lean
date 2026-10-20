import SymmetricSubgroupAsymptotics.PermutationalWreathProduct
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Group.Pi.Basic

/-! Exact affine coordinates for an arbitrary permutational wreath.
The translation function and the full local linear tuple are retained.
Restricting the resulting equivalence to any subgroup therefore retains
its actual translation kernel and its actual projected subgroup. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PermutationalWreathAffineCoordinates

open SemidirectProduct

variable {V A R I : Type} [CommGroup V] [Group A] [Group R] [MulAction R I]
  (φ : A →* MulAut V)

abbrev Linear := PermutationalWreathProduct A R I

def action : Linear (A := A) (R := R) (I := I) →* MulAut (I → V) where
  toFun w :=
    { toFun := fun v i => φ (w.left i) (v (w.right⁻¹ • i))
      invFun := fun v i => (φ (w.left (w.right • i))).symm (v (w.right • i))
      left_inv := by
        intro v
        funext i
        simp only [inv_smul_smul,MulEquiv.symm_apply_apply]
      right_inv := by
        intro v
        funext i
        simp only [smul_inv_smul,MulEquiv.apply_symm_apply]
      map_mul' := by
        intro v u
        funext i
        exact map_mul _ _ _ }
  map_one' := by
    apply MulEquiv.ext
    intro v
    funext i
    change φ 1 (v ((1 : R)⁻¹ • i)) = v i
    rw [inv_one,one_smul,map_one]
    rfl
  map_mul' w z := by
    apply MulEquiv.ext
    intro v
    funext i
    change φ (w.left i * z.left (w.right⁻¹ • i))
      (v ((w.right*z.right)⁻¹ • i)) =
      φ (w.left i) (φ (z.left (w.right⁻¹ • i))
        (v (z.right⁻¹ • (w.right⁻¹ • i))))
    rw [map_mul,mul_inv_rev,mul_smul]
    rfl

@[simp] theorem action_apply (w : Linear (A := A) (R := R) (I := I))
    (v : I → V) (i : I) : action φ w v i = φ (w.left i) (v (w.right⁻¹ • i)) := rfl

abbrev Model := (I → V) ⋊[action (R := R) (I := I) φ] Linear (A := A) (R := R) (I := I)
abbrev Local := V ⋊[φ] A

def intoWreath : Model (R := R) (I := I) φ →*
    PermutationalWreathProduct (Local φ) R I where
  toFun g := ⟨fun i => ⟨g.left i,g.right.left i⟩,g.right.right⟩
  map_one' := by
    apply PermutationalWreathProduct.ext
    · funext i
      apply SemidirectProduct.ext <;> rfl
    · rfl
  map_mul' g h := by
    apply PermutationalWreathProduct.ext
    · funext i
      apply SemidirectProduct.ext <;> rfl
    · rfl

theorem intoWreath_injective : Function.Injective (intoWreath (R := R) (I := I) φ) := by
  intro g h he
  apply SemidirectProduct.ext
  · funext i
    exact congrArg (fun z : PermutationalWreathProduct (Local φ) R I => (z.left i).left) he
  · apply PermutationalWreathProduct.ext
    · funext i
      exact congrArg (fun z : PermutationalWreathProduct (Local φ) R I => (z.left i).right) he
    · exact congrArg (fun z : PermutationalWreathProduct (Local φ) R I => z.right) he

theorem intoWreath_surjective : Function.Surjective (intoWreath (R := R) (I := I) φ) := by
  intro w
  refine ⟨⟨fun i => (w.left i).left,⟨fun i => (w.left i).right,w.right⟩⟩,?_⟩
  apply PermutationalWreathProduct.ext
  · funext i
    apply SemidirectProduct.ext <;> rfl
  · rfl

def equiv : Model (R := R) (I := I) φ ≃*
    PermutationalWreathProduct (Local φ) R I :=
  MulEquiv.ofBijective (intoWreath φ) ⟨intoWreath_injective φ,intoWreath_surjective φ⟩

theorem action_injective [DecidableEq I] [Nontrivial V] [FaithfulSMul R I]
    (hφ : Function.Injective φ) :
    Function.Injective (action (R := R) (I := I) φ) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have hr : w.right = 1 := by
    apply eq_of_smul_eq_smul (M := R) (α := I)
    intro i
    simp only [one_smul]
    by_contra hi
    obtain ⟨v,hv⟩ := exists_ne (1 : V)
    have he := congrArg (fun f : MulAut (I → V) => f (Pi.mulSingle i v) (w.right • i)) hw
    have hv' : φ (w.left (w.right • i)) v = 1 := by
      change φ (w.left (w.right • i))
        ((Pi.mulSingle i v : I → V) (w.right⁻¹ • (w.right • i))) =
          (Pi.mulSingle i v : I → V) (w.right • i) at he
      rw [inv_smul_smul,Pi.mulSingle_eq_same,Pi.mulSingle_eq_of_ne hi] at he
      exact he
    exact hv ((φ (w.left (w.right • i))).injective
      (hv'.trans (map_one _).symm))
  apply PermutationalWreathProduct.ext
  · funext i
    apply hφ
    apply MulEquiv.ext
    intro v
    have he := congrArg (fun f : MulAut (I → V) => f (Pi.mulSingle i v) i) hw
    change φ (w.left i) ((Pi.mulSingle i v : I → V) (w.right⁻¹ • i)) =
      (Pi.mulSingle i v : I → V) i at he
    rw [hr,inv_one,one_smul,Pi.mulSingle_eq_same] at he
    change φ (w.left i) v = φ 1 v
    rw [map_one]
    exact he
  · exact hr

end SymmetricSubgroupAsymptotics.PermutationalWreathAffineCoordinates

end
