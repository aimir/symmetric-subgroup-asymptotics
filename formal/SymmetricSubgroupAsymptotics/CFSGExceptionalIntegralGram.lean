import SymmetricSubgroupAsymptotics.CFSGExceptionalCartanPositiveDefinite
import SymmetricSubgroupAsymptotics.CFSGIntegralGramFinite

/-! A denominator-cleared actual E₈ Gram embedding. Its integer norm-two
vectors form a finite type by an output-box argument, without enumerating
any roots. Supported subsets give finite candidate E₆/E₇ root types too. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalIntegralGram
open CFSGExceptionalCartanPositiveDefinite

 def integerRows : Matrix (Fin 8) (Fin 8) ℤ :=
  !![1,-1,-1,-1,-1,-1,-1,1;
     2,2,0,0,0,0,0,0;
     -2,2,0,0,0,0,0,0;
     0,-2,2,0,0,0,0,0;
     0,0,-2,2,0,0,0,0;
     0,0,0,-2,2,0,0,0;
     0,0,0,0,-2,2,0,0;
     0,0,0,0,0,-2,2,0]
 def integerColumns : Matrix (Fin 8) (Fin 8) ℤ := integerRows.transpose

 theorem integerColumns_cast : (Int.castRingHom ℚ).mapMatrix integerColumns=
    (2:ℚ) • rootColumns := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [integerColumns,integerRows,rootColumns,rootRows]

 theorem integerColumns_gram : integerColumns.transpose*integerColumns=
    (4:ℤ) • CartanMatrix.E₈ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [integerColumns,integerRows,CartanMatrix.E₈,Matrix.mul_apply,Fin.sum_univ_succ]

 theorem integerColumns_injective : Function.Injective integerColumns.mulVec := by
  intro x y h
  have hc : rootColumns*ᵥ(fun i=>(x i:ℚ))=rootColumns*ᵥ(fun i=>(y i:ℚ)) := by
    ext i
    have hi := congrArg (Int.castRingHom ℚ) (congrFun h i)
    try dsimp only at hi
    simp only [RingHom.map_mulVec] at hi
    change (((Int.castRingHom ℚ).mapMatrix integerColumns)*ᵥ(fun j=>(x j:ℚ))) i=
      (((Int.castRingHom ℚ).mapMatrix integerColumns)*ᵥ(fun j=>(y j:ℚ))) i at hi
    rw [integerColumns_cast] at hi
    simp only [Matrix.smul_mulVec,Pi.smul_apply,smul_eq_mul] at hi
    exact mul_left_cancel₀ (by norm_num : (2:ℚ)≠0) hi
  have hxy := rootColumns_injective hc
  ext i
  exact_mod_cast congrFun hxy i

 theorem energy_eq_four_norm (x : Fin 8→ℤ) :
    (∑i,(integerColumns*ᵥx) i^2)=4*(x ⬝ᵥ(CartanMatrix.E₈*ᵥx)) := by
  calc
    (∑i,(integerColumns*ᵥx) i^2)=(integerColumns*ᵥx) ⬝ᵥ(integerColumns*ᵥx) := by
      simp only [dotProduct,pow_two]
    _=x ⬝ᵥ(integerColumns.transpose*ᵥ(integerColumns*ᵥx)) := by
      exact (Matrix.dotProduct_transpose_mulVec integerColumns x (integerColumns*ᵥx)).symm
    _=x ⬝ᵥ((integerColumns.transpose*integerColumns)*ᵥx) := by
      rw [←Matrix.mulVec_mulVec]
    _=4*(x ⬝ᵥ(CartanMatrix.E₈*ᵥx)) := by
      rw [integerColumns_gram,Matrix.smul_mulVec,dotProduct_smul]
      simp only [zsmul_eq_mul]
      norm_num

 def Roots := {x : Fin 8→ℤ // x ⬝ᵥ(CartanMatrix.E₈*ᵥx)=2}

 theorem roots_finite : {x : Fin 8→ℤ | x ⬝ᵥ(CartanMatrix.E₈*ᵥx)=2}.Finite := by
  apply (CFSGIntegralGramFinite.finite_energy_level integerColumns integerColumns_injective 8).subset
  intro x hx
  change (∑i,(integerColumns*ᵥx) i^2)=(8:ℤ)
  rw [energy_eq_four_norm,hx]
  norm_num

 instance : Finite Roots := roots_finite.to_subtype

 def SupportedRoots (n : ℕ) := {x : Roots // ∀ i : Fin 8, n ≤ i.val → x.val i=0}
 instance (n : ℕ) : Finite (SupportedRoots n) := inferInstanceAs (Finite {x : Roots // _})

end SymmetricSubgroupAsymptotics.CFSGExceptionalIntegralGram
