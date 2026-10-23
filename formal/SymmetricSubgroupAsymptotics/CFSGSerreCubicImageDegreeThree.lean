import SymmetricSubgroupAsymptotics.CFSGSerreCubicMatrixOperators

/-! A proved rational fourth adjoint on a genuine cubic Serre image
descends to the SAME integral lattice and every tensor base change.
All mapped divided-power coefficients of degree at least four vanish;
the actual third coefficient is retained in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGSerreCubicMatrix
open CFSG.Models.Chevalley
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)
    (hfour : ∀neg i (x : RationalLie A),
      (LieAlgebra.ad ℚ (Matrix I I ℚ) (fieldRoot D ℚ neg i)^4) (D.rational x)=0)

include hfour

theorem rational_image_operator_ge_four (neg : Bool) (i : Fin n) (k : ℕ) (hk : 4≤k)
    (x : RationalLie A) :
    CFSGIntegralCubicRootOperators.operator ℚ (fieldRoot D ℚ neg i)
      (fieldSecond D ℚ neg i) (fieldThird D ℚ neg i) k (D.rational x)=0 := by
  let T : Module.End ℚ (Matrix I I ℚ) := LieAlgebra.ad ℚ (Matrix I I ℚ) (fieldRoot D ℚ neg i)
  have hpow4 : (T^4) (D.rational x)=0 := hfour neg i x
  have hpowk : (T^k) (D.rational x)=0 := by
    obtain ⟨m,hm⟩ : ∃m : ℕ,k=m+4 := ⟨k-4,by omega⟩
    rw [hm,pow_add,Module.End.mul_apply,hpow4,map_zero]
  have hh := CFSGCubicRootDividedPowers.ad_pow_eq_factorial_operator
    (fieldRoot D ℚ neg i) (fieldSecond D ℚ neg i) (fieldThird D ℚ neg i) (fieldRoot_square D ℚ neg i)
    (fieldRoot_mul_second D ℚ neg i) (fieldSecond_mul_root D ℚ neg i)
    (fieldRoot_mul_third D ℚ neg i) (fieldThird_mul_root D ℚ neg i) k (D.rational x)
  change (T^k) (D.rational x)=_ at hh
  rw [hpowk] at hh
  exact (smul_eq_zero.mp hh.symm).resolve_left (by exact_mod_cast Nat.factorial_ne_zero k)

theorem integral_image_operator_ge_four (neg : Bool) (i : Fin n) (k : ℕ) (hk : 4≤k)
    (x : integralLattice A) : integralRepresentation D (integralOperator A neg i k x)=0 := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective I
  rw [integralRepresentation_cast,map_zero]
  change D.rational (dividedPower A neg i k x.val)=0
  rw [CFSGSerreIntegralRepresentation.dividedPower_intertwines,rational_rootVector,
    CFSGCubicRootDividedPowers.rational_operator _ _ _ (fieldRoot_square D ℚ neg i)
      (fieldRoot_mul_second D ℚ neg i) (fieldSecond_mul_root D ℚ neg i)
      (fieldRoot_mul_third D ℚ neg i) (fieldThird_mul_root D ℚ neg i)]
  exact rational_image_operator_ge_four D hfour neg i k hk x.val

theorem baseChange_integralOperator_ge_four (K : Type*) [CommRing K]
    (neg : Bool) (i : Fin n) (k : ℕ) (hk : 4≤k) (x : K⊗[ℤ]integralLattice A) :
    baseChange D K ((integralOperator A neg i k).baseChange K x)=0 := by
  induction x using TensorProduct.induction_on with
  | zero=>simp only [map_zero]
  | tmul a x=>
    rw [LinearMap.baseChange_tmul,baseChange_tmul,integral_image_operator_ge_four D hfour neg i k hk,
      map_zero,smul_zero]
  | add x y hx hy=>simp only [map_add,hx,hy,add_zero]

theorem baseChange_image_operator_ge_four (K : Type*) [CommRing K]
    (neg : Bool) (i : Fin n) (k : ℕ) (hk : 4≤k) (x : K⊗[ℤ]integralLattice A) :
    CFSGIntegralCubicRootOperators.operator K (fieldRoot D K neg i)
      (fieldSecond D K neg i) (fieldThird D K neg i) k (baseChange D K x)=0 := by
  rw [←baseChange_operator D K neg i k x]
  exact baseChange_integralOperator_ge_four D hfour K neg i k hk x

theorem baseChange_rootOperator_conjugation (K : Type) [Field K]
    (neg : Bool) (i : Fin n) (t : K) (x : Space A K) :
    baseChange D K (rootOperator A K neg i t x)=
      CFSGIntegralCubicRootOperators.exponential K (fieldRoot D K neg i)
          (fieldSecond D K neg i) (fieldThird D K neg i) t * baseChange D K x *
        CFSGIntegralCubicRootOperators.exponential K (fieldRoot D K neg i)
          (fieldSecond D K neg i) (fieldThird D K neg i) (-t) := by
  rw [rootOperator]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,baseChange_operator]
  have hz (k : ℕ) (hk : 4≤k) := baseChange_image_operator_ge_four D hfour K neg i k hk x
  have hh := CFSGIntegralCubicRootOperators.operator_sum_eq_conjugation K t
    (fieldRoot D K neg i) (fieldSecond D K neg i) (fieldThird D K neg i) (baseChange D K x)
  simpa only [Finset.sum_range_succ,Finset.sum_range_zero,hz 4 (by omega),hz 5 (by omega),
    hz 6 (by omega),smul_zero,add_zero] using hh

end SymmetricSubgroupAsymptotics.CFSGSerreCubicMatrix
