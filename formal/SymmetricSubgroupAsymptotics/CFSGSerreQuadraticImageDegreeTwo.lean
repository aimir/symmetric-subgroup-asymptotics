import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrixOperators

/-! A proved rational adjoint cube on a quadratic Serre image descends
to the SAME integral lattice image and every tensor base change. All
mapped divided-power coefficients of degree at least three vanish.
Only the rational verification uses factorial cancellation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
open CFSG.Models.Chevalley
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)
    (hthree : ∀neg i (x : RationalLie A),
      ⁅fieldRoot D ℚ neg i,⁅fieldRoot D ℚ neg i,⁅fieldRoot D ℚ neg i,D.rational x⁆⁆⁆=0)

include hthree

theorem rational_image_operator_ge_three (neg : Bool) (i : Fin n) (k : ℕ) (hk : 3≤k)
    (x : RationalLie A) :
    CFSGIntegralQuadraticRootOperators.operator ℚ (fieldRoot D ℚ neg i)
      (fieldSecond D ℚ neg i) k (D.rational x)=0 := by
  let T : Module.End ℚ (Matrix I I ℚ) := LieAlgebra.ad ℚ (Matrix I I ℚ) (fieldRoot D ℚ neg i)
  have hpow3 : (T^3) (D.rational x)=0 := hthree neg i x
  have hpowk : (T^k) (D.rational x)=0 := by
    obtain ⟨m,hm⟩ : ∃m : ℕ,k=m+3 := ⟨k-3,by omega⟩
    rw [hm,pow_add,Module.End.mul_apply,hpow3,map_zero]
  have hh := CFSGQuadraticRootDividedPowers.ad_pow_eq_factorial_operator
    (fieldRoot D ℚ neg i) (fieldSecond D ℚ neg i) (fieldRoot_square D ℚ neg i)
    (fieldRoot_mul_second D ℚ neg i) (fieldSecond_mul_root D ℚ neg i) k (D.rational x)
  change (T^k) (D.rational x)=_ at hh
  rw [hpowk] at hh
  exact (smul_eq_zero.mp hh.symm).resolve_left (by exact_mod_cast Nat.factorial_ne_zero k)

theorem integral_image_operator_ge_three (neg : Bool) (i : Fin n) (k : ℕ) (hk : 3≤k)
    (x : integralLattice A) : integralRepresentation D (integralOperator A neg i k x)=0 := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective I
  rw [integralRepresentation_cast,map_zero]
  change D.rational (dividedPower A neg i k x.val)=0
  rw [CFSGSerreIntegralRepresentation.dividedPower_intertwines,rational_rootVector,
    CFSGQuadraticRootDividedPowers.rational_operator _ _ (fieldRoot_square D ℚ neg i)
      (fieldRoot_mul_second D ℚ neg i) (fieldSecond_mul_root D ℚ neg i)]
  exact rational_image_operator_ge_three D hthree neg i k hk x.val

theorem baseChange_integralOperator_ge_three (K : Type*) [CommRing K]
    (neg : Bool) (i : Fin n) (k : ℕ) (hk : 3≤k) (x : K⊗[ℤ]integralLattice A) :
    baseChange D K ((integralOperator A neg i k).baseChange K x)=0 := by
  induction x using TensorProduct.induction_on with
  | zero=>simp only [map_zero]
  | tmul a x=>
    rw [LinearMap.baseChange_tmul,baseChange_tmul,integral_image_operator_ge_three D hthree neg i k hk,
      map_zero,smul_zero]
  | add x y hx hy=>simp only [map_add,hx,hy,add_zero]

theorem baseChange_image_operator_ge_three (K : Type*) [CommRing K]
    (neg : Bool) (i : Fin n) (k : ℕ) (hk : 3≤k) (x : K⊗[ℤ]integralLattice A) :
    CFSGIntegralQuadraticRootOperators.operator K (fieldRoot D K neg i)
      (fieldSecond D K neg i) k (baseChange D K x)=0 := by
  rw [←baseChange_operator D K neg i k x]
  exact baseChange_integralOperator_ge_three D hthree K neg i k hk x

theorem baseChange_rootOperator_degree_two (K : Type) [Field K]
    (neg : Bool) (i : Fin n) (t : K) (x : Space A K) :
    baseChange D K (rootOperator A K neg i t x)=baseChange D K x+
      t • CFSGIntegralQuadraticRootOperators.operator K (fieldRoot D K neg i)
        (fieldSecond D K neg i) 1 (baseChange D K x)+
      t^2 • CFSGIntegralQuadraticRootOperators.operator K (fieldRoot D K neg i)
        (fieldSecond D K neg i) 2 (baseChange D K x) := by
  rw [rootOperator]
  simp only [LinearMap.sum_apply,LinearMap.add_apply,LinearMap.smul_apply,map_sum,map_add,map_smul,baseChange_operator,
    Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,one_smul,
    CFSGIntegralQuadraticRootOperators.operator_zero,
    baseChange_image_operator_ge_three D hthree K neg i 3 (by omega) x,smul_zero,add_zero]

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
