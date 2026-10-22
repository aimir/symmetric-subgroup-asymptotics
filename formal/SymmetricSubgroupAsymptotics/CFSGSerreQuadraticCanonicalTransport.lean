import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticSourceTransport
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalWeyl

/-! Changing only the proved Cartan source leaves every literal integer
root, second coefficient and canonical root/Weyl matrix unchanged. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
variable {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I]
    (h : A=B) (D : Data A I)

theorem fieldRoot_transportSource (K : Type*) [CommRing K] (neg : Bool) (i : Fin n) :
    fieldRoot (transportSource h D) K neg i=fieldRoot D K neg i := by cases h;rfl

theorem fieldSecond_transportSource (K : Type*) [CommRing K] (neg : Bool) (i : Fin n) :
    fieldSecond (transportSource h D) K neg i=fieldSecond D K neg i := by cases h;rfl

theorem canonicalRoot_transportSource (K : Type*) [CommRing K] (neg : Bool) (i : Fin n) (t : K) :
    canonicalRoot (transportSource h D) K neg i t=canonicalRoot D K neg i t := by cases h;rfl

theorem canonicalWeyl_transportSource (K : Type*) [CommRing K] (i : Fin n) :
    canonicalWeyl (transportSource h D) K i=canonicalWeyl D K i := by cases h;rfl

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
