import SymmetricSubgroupAsymptotics.CFSGNormTwoLatticeReflections
import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixPairing
import Mathlib.LinearAlgebra.RootSystem.IsValuedIn

/-! The actual rational root pairing of the norm-two integer lattice.
Its index is the literal norm-two vector subtype and its reflections are
proved integral permutations. A finite base and named Cartan identification
are separate obligations; none is hidden in this construction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoRootPairing
open CFSGIntegerMatrixPairing
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)

 abbrev Roots := CFSGNormTwoLatticeReflections.Roots (integerPairing A)

 def rootEmbedding : Roots A↪(n→ℚ) where
  toFun x := castVector x.val
  inj' x y h := Subtype.ext (castVector_injective h)

 def rootPairing : RootPairing (Roots A) ℚ (n→ℚ) (n→ℚ) where
  toLinearMap := rationalPairing A
  isPerfPair_toLinearMap := rationalPairing_perfect A hs hp
  root := rootEmbedding A
  coroot := rootEmbedding A
  root_coroot_two := by
    intro i
    change rationalPairing A (castVector i.val) (castVector i.val)=2
    rw [cast_pairing,i.property]
    norm_num
  reflectionPerm := CFSGNormTwoLatticeReflections.reflectionPerm
    (integerPairing A) (integer_symmetric A hs)
  reflectionPerm_root := by
    intro i j
    change castVector j.val-rationalPairing A (castVector j.val) (castVector i.val) • castVector i.val=
      castVector (j.val-integerPairing A j.val i.val • i.val)
    exact (cast_reflection A i.val j.val).symm
  reflectionPerm_coroot := by
    intro i j
    change castVector j.val-rationalPairing A (castVector i.val) (castVector j.val) • castVector i.val=
      castVector (j.val-integerPairing A j.val i.val • i.val)
    rw [rational_symmetric A hs (castVector i.val) (castVector j.val)]
    exact (cast_reflection A i.val j.val).symm

 theorem pairing_cast (i j : Roots A) :
    (rootPairing A hs hp).pairing i j=(integerPairing A i.val j.val:ℚ) :=
  cast_pairing A i.val j.val

 instance rootPairing_isCrystallographic : (rootPairing A hs hp).IsCrystallographic where
  exists_value i j := by
    refine ⟨integerPairing A i.val j.val,?_⟩
    exact (pairing_cast A hs hp i j).symm

end SymmetricSubgroupAsymptotics.CFSGNormTwoRootPairing
