import SymmetricSubgroupAsymptotics.CFSGQuadraticWeylParameterConjugacy
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalRootAdditive
import Mathlib.GroupTheory.Commutator.Basic

/-! The literal commutator of a Weyl-square and an adjacent root is the
root at parameter -2t. This is a proved matrix-word identity, rather than
an assumed membership in a derived fixed subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)
    (i j : Fin n) (neg : Bool)
    (he : (canonicalWeyl D ℚ i : Matrix I I ℚ)^2*fieldRoot D ℚ neg j=
      -(fieldRoot D ℚ neg j*(canonicalWeyl D ℚ i : Matrix I I ℚ)^2))
include he

theorem canonical_weyl_square_commutator (K : Type*) [CommRing K] (t : K) :
    ⁅(canonicalWeyl D K i)^2,canonicalRoot D K neg j t⁆=
      canonicalRoot D K neg j (-(2*t)) := by
  rw [commutatorElement_def,canonical_weyl_square_root D i j neg he K t]
  rw [mul_assoc (canonicalRoot D K neg j (-t)) ((canonicalWeyl D K i)^2)
      (((canonicalWeyl D K i)^2)⁻¹),
    mul_inv_cancel,mul_one,canonicalRoot_inverse,canonicalRoot_add]
  congr 1
  ring

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
