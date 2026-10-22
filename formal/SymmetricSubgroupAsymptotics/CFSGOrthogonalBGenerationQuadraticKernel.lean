import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationBlockRestriction
import Mathlib.Data.Matrix.Basis

/-! The transpose quadratic form detects the kernel of hyperplane
restriction. In characteristic two the bilinear form alone would not
detect the last column, so this argument keeps its quadratic refinement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationQuadraticKernel
open Matrix CFSGOrthogonalBGenerationBlockRestriction
variable (K : Type*) [Field K] (n : Type*) [Fintype n] [DecidableEq n]

abbrev QIndex := (n ⊕ n) ⊕ Unit
abbrev QMatrix := Matrix (QIndex n) (QIndex n) K

def quadratic (v : QIndex n → K) : K :=
  (∑ i, v (Sum.inl (Sum.inl i)) * v (Sum.inl (Sum.inr i))) + v (Sum.inr ()) ^ 2

def transposeIsometries : Subgroup (QMatrix K n)ˣ where
  carrier := {g | ∀ v, quadratic K n ((g : QMatrix K n)ᵀ *ᵥ v) = quadratic K n v}
  one_mem' := by intro v; simp
  mul_mem' := by
    intro a b ha hb v
    change quadratic K n (((a : QMatrix K n) * (b : QMatrix K n))ᵀ *ᵥ v) = _
    rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec, hb, ha]
  inv_mem' := by
    intro g hg v
    have hm : (g : QMatrix K n)ᵀ * (↑g⁻¹ : QMatrix K n)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
    have hh := hg ((↑g⁻¹ : QMatrix K n)ᵀ *ᵥ v)
    rw [Matrix.mulVec_mulVec, hm, Matrix.one_mulVec] at hh
    exact hh.symm

theorem eq_one_of_upperBlock_eq_one (A : QMatrix K n)
    (hrow : FixedLastRow K (n ⊕ n) A)
    (hblock : upperBlock K (n ⊕ n) A = 1)
    (hQ : ∀ v, quadratic K n (Aᵀ *ᵥ v) = quadratic K n v) : A = 1 := by
  have hb (x y : n ⊕ n) : A (Sum.inl x) (Sum.inl y) =
      (1 : Matrix (n ⊕ n) (n ⊕ n) K) x y :=
    congrArg (fun M : Matrix (n ⊕ n) (n ⊕ n) K => M x y) hblock
  have hp (i : n) : A (Sum.inl (Sum.inl i)) (Sum.inr ()) = 0 := by
    have hh := hQ (Pi.single (Sum.inl (Sum.inl i)) 1)
    have hs : A (Sum.inl (Sum.inl i)) (Sum.inr ()) ^ 2 = 0 := by
      simpa [quadratic, Matrix.mulVec_single_one, Matrix.col_apply,
        Matrix.transpose_apply, hb, Matrix.one_apply, Pi.single_apply] using hh
    exact eq_zero_of_pow_eq_zero hs
  have hn (i : n) : A (Sum.inl (Sum.inr i)) (Sum.inr ()) = 0 := by
    have hh := hQ (Pi.single (Sum.inl (Sum.inr i)) 1)
    have hs : A (Sum.inl (Sum.inr i)) (Sum.inr ()) ^ 2 = 0 := by
      simpa [quadratic, Matrix.mulVec_single_one, Matrix.col_apply,
        Matrix.transpose_apply, hb, Matrix.one_apply, Pi.single_apply] using hh
    exact eq_zero_of_pow_eq_zero hs
  ext x y
  rcases x with (x | ⟨⟩)
  · rcases y with (y | ⟨⟩)
    · simpa only [Matrix.one_apply, Sum.inl.injEq] using hb x y
    · rcases x with (i | i) <;> simp [hp, hn, Matrix.one_apply]
  · simpa [Matrix.one_apply, eq_comm] using hrow y

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationQuadraticKernel
