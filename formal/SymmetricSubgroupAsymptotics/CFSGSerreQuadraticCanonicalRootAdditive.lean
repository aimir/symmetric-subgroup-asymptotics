import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalRoots
import SymmetricSubgroupAsymptotics.CFSGQuadraticRootAdditive

/-! Additive parameter and inverse formulas for the literal canonical
integral quadratic roots, with no restriction on characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)

theorem canonicalRoot_add (K : Type*) [CommRing K] (neg : Bool) (i : Fin n) (t u : K) :
    canonicalRoot D K neg i t*canonicalRoot D K neg i u=canonicalRoot D K neg i (t+u) :=
  CFSGQuadraticRootExponential.rootUnit_add _ _ (fieldRoot_square D K neg i)
    (fieldRoot_mul_second D K neg i) (fieldSecond_mul_root D K neg i)
    (fieldSecond_square D K neg i) t u

theorem canonicalRoot_inverse (K : Type*) [CommRing K] (neg : Bool) (i : Fin n) (t : K) :
    (canonicalRoot D K neg i t)⁻¹=canonicalRoot D K neg i (-t) := by
  apply Units.ext
  rw [canonicalRoot_inv_val,canonicalRoot_val]
  simp only [neg_smul,neg_sq,sub_eq_add_neg]

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
