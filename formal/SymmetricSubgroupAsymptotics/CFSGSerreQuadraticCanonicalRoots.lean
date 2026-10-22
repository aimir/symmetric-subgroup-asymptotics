import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrixActions
import SymmetricSubgroupAsymptotics.CFSGQuadraticRootExponential

/-! Canonical elementary roots for any proved integral quadratic Serre
matrix datum. The actual unit and its inverse use the integral polynomial,
so this construction also works in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)

def canonicalRoot (K : Type*) [CommRing K] (neg : Bool) (i : Fin n) (t : K) :
    (Matrix I I K)ˣ :=
  CFSGQuadraticRootExponential.rootUnit (fieldRoot D K neg i) (fieldSecond D K neg i)
    (fieldRoot_square D K neg i) (fieldRoot_mul_second D K neg i)
    (fieldSecond_mul_root D K neg i) (fieldSecond_square D K neg i) t

theorem canonicalRoot_val (K : Type*) [CommRing K] (neg : Bool) (i : Fin n) (t : K) :
    (canonicalRoot D K neg i t : Matrix I I K)=
      1+t • fieldRoot D K neg i+t^2 • fieldSecond D K neg i := rfl

theorem canonicalRoot_inv_val (K : Type*) [CommRing K] (neg : Bool) (i : Fin n) (t : K) :
    (↑((canonicalRoot D K neg i t)⁻¹):Matrix I I K)=
      1-t • fieldRoot D K neg i+t^2 • fieldSecond D K neg i :=
  CFSGQuadraticRootExponential.rootUnit_inv_val _ _ _ _ _ _ t

variable (K : Type) [Field K]
abbrev canonicalElementaryGroup := elementaryGroup K (canonicalRoot D K)
abbrev canonicalElementaryRoot := elementaryRoot K (canonicalRoot D K)

variable (hfour : ∀neg i (x : CFSG.Models.Chevalley.Space A K),
  fieldSecond D K neg i*baseChange D K x*fieldSecond D K neg i=0)

def canonicalImageAction : canonicalElementaryGroup D K→*
    ((baseChange D K).range≃ₗ[K](baseChange D K).range) :=
  elementaryImageAction D K (canonicalRoot D K) (canonicalRoot_val D K)
    (canonicalRoot_inv_val D K) hfour

theorem canonical_action_ranges_eq :
    (imageRepresentation D K).range=(canonicalImageAction D K hfour).range :=
  action_ranges_eq D K (canonicalRoot D K) (canonicalRoot_val D K)
    (canonicalRoot_inv_val D K) hfour

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
