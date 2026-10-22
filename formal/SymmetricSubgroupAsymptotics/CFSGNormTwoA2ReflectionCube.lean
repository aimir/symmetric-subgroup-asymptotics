import SymmetricSubgroupAsymptotics.CFSGA2ReflectionCube
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylCharTwoRoots

/-! The cube of two adjacent actual root reflections is identity. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoA2ReflectionCube
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckWeylCharTwoRoots
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)

theorem adjacent_reflection_cube (i j : Roots A)
    (hij : integerPairing A i.val j.val= -1) (k : Roots A) :
    (rootPairing A hs hp).reflectionPerm i ((rootPairing A hs hp).reflectionPerm j
      ((rootPairing A hs hp).reflectionPerm i ((rootPairing A hs hp).reflectionPerm j
        ((rootPairing A hs hp).reflectionPerm i ((rootPairing A hs hp).reflectionPerm j k)))))=k := by
  apply Subtype.ext
  have hji : integerPairing A j.val i.val= -1 := by
    rw [integer_symmetric A hs];exact hij
  simpa only [reflection_val,CFSGNormTwoLatticeReflections.reflection] using
    CFSGA2ReflectionCube.reflection_cube (integerPairing A) i.val j.val
      i.property j.property hij hji k.val

end SymmetricSubgroupAsymptotics.CFSGNormTwoA2ReflectionCube
