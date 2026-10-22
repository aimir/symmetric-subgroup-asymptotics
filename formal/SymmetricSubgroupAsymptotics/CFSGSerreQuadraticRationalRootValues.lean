import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalWeyl

/-! The actual rational value and cube of a canonical integral
quadratic root unit, exposing the half-square only over the rationals. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)

theorem fieldRoot_cube (K : Type*) [CommRing K] (neg : Bool) (i : Fin r) :
    (fieldRoot D K neg i)^3=0 := by
  rw [pow_succ,pow_two,fieldRoot_square,add_mul,fieldSecond_mul_root,add_zero]

theorem canonicalRoot_val_rational (neg : Bool) (i : Fin r) (a : ℚ) :
    (canonicalRoot D ℚ neg i a : Matrix I I ℚ)=
      1+a • fieldRoot D ℚ neg i+(a^2/2) • (fieldRoot D ℚ neg i)^2 := by
  have hd : fieldSecond D ℚ neg i=(1/2:ℚ) • (fieldRoot D ℚ neg i*fieldRoot D ℚ neg i) := by
    calc
      _=(1/2:ℚ) • (fieldSecond D ℚ neg i+fieldSecond D ℚ neg i) := by module
      _=_ := by rw [fieldRoot_square]
  rw [canonicalRoot_val,hd,smul_smul,show a^2*(1/2:ℚ)=a^2/2 by ring]
  simp only [pow_two]

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
