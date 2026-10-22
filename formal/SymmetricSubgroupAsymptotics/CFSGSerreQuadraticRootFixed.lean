import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalRoots

/-! An actual quadratic root unit fixes its own root matrix by conjugation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)

theorem canonicalRoot_fixes_root (K : Type*) [CommRing K] (neg : Bool) (i : Fin n) (t : K) :
    (canonicalRoot D K neg i t : Matrix I I K)*fieldRoot D K neg i*
      (↑((canonicalRoot D K neg i t)⁻¹):Matrix I I K)=fieldRoot D K neg i := by
  have hc : (canonicalRoot D K neg i t : Matrix I I K)*fieldRoot D K neg i=
      fieldRoot D K neg i*(canonicalRoot D K neg i t : Matrix I I K) := by
    simp only [canonicalRoot_val,add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,
      mul_smul_comm,fieldRoot_mul_second,fieldSecond_mul_root,smul_zero,add_zero]
  rw [hc,mul_assoc,Units.mul_inv,mul_one]

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
