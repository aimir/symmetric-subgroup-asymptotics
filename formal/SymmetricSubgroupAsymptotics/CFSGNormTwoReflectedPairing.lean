import SymmetricSubgroupAsymptotics.CFSGNormTwoRootPairing
import Mathlib.Tactic.Ring

/-! The exact coroot-pairing identity under the actual lattice
reflection. All coefficients remain integral. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoReflectedPairing
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)

theorem reflected_pairing (i j k : Roots A) :
    integerPairing A j.val ((rootPairing A hs hp).reflectionPerm i k).val-
      integerPairing A j.val i.val*
        integerPairing A i.val ((rootPairing A hs hp).reflectionPerm i k).val=
      integerPairing A j.val k.val := by
  change integerPairing A j.val (k.val-integerPairing A k.val i.val • i.val)-
    integerPairing A j.val i.val*
      integerPairing A i.val (k.val-integerPairing A k.val i.val • i.val)=_
  simp only [map_sub,map_smul,smul_eq_mul,i.property,
    integer_symmetric A hs k.val i.val]
  ring

end SymmetricSubgroupAsymptotics.CFSGNormTwoReflectedPairing
