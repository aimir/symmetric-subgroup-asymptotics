import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-! Integer matrix pairings and their rational scalar extension. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGIntegerMatrixPairing
variable {n : Type*} [Fintype n] [DecidableEq n]

 def integerPairing (A : Matrix n n ℤ) : LinearMap.BilinForm ℤ (n→ℤ) := A.toBilin'
 def rationalMatrix (A : Matrix n n ℤ) : Matrix n n ℚ := (Int.castRingHom ℚ).mapMatrix A
 def rationalPairing (A : Matrix n n ℤ) : LinearMap.BilinForm ℚ (n→ℚ) := (rationalMatrix A).toBilin'
 def castVector (x : n→ℤ) : n→ℚ := fun i=>(x i:ℚ)

 theorem castVector_injective : Function.Injective (castVector (n:=n)) := by
  intro x y h
  ext i
  have hi := congrFun h i
  change (x i:ℚ)=(y i:ℚ) at hi
  exact_mod_cast hi

 theorem cast_pairing (A : Matrix n n ℤ) (x y : n→ℤ) :
    rationalPairing A (castVector x) (castVector y)=(integerPairing A x y:ℚ) := by
  simp [integerPairing,rationalPairing,rationalMatrix,castVector,Matrix.toBilin'_apply]

 theorem integer_symmetric (A : Matrix n n ℤ) (hA : A.transpose=A) (x y : n→ℤ) :
    integerPairing A x y=integerPairing A y x := by
  simp only [integerPairing,Matrix.toBilin'_apply']
  simpa only [hA] using (Matrix.dotProduct_transpose_mulVec A y x).symm

 theorem rational_symmetric (A : Matrix n n ℤ) (hA : A.transpose=A) (x y : n→ℚ) :
    rationalPairing A x y=rationalPairing A y x := by
  have hq : (rationalMatrix A).transpose=rationalMatrix A := by
    change A.transpose.map (Int.castRingHom ℚ)=A.map (Int.castRingHom ℚ)
    rw [hA]
  simp only [rationalPairing,Matrix.toBilin'_apply']
  simpa only [hq] using (Matrix.dotProduct_transpose_mulVec (rationalMatrix A) y x).symm

 theorem cast_reflection (A : Matrix n n ℤ) (a x : n→ℤ) :
    castVector (x-integerPairing A x a • a)=
      castVector x-rationalPairing A (castVector x) (castVector a) • castVector a := by
  rw [cast_pairing]
  ext i
  simp [castVector,Pi.smul_apply,zsmul_eq_mul]

 theorem rationalPairing_injective (A : Matrix n n ℤ) (hA : (rationalMatrix A).PosDef) :
    Function.Injective (rationalPairing A) := by
  intro x y h
  have hlin : rationalPairing A (x-y)=0 := by rw [map_sub,h,sub_self]
  have hz : rationalPairing A (x-y) (x-y)=0 := by
    rw [hlin,LinearMap.zero_apply]
  by_contra hxy
  have hne : x-y≠0 := sub_ne_zero.mpr hxy
  have hp : 0<rationalPairing A (x-y) (x-y) := by
    simpa only [rationalPairing,Matrix.toBilin'_apply',star_trivial] using
      hA.dotProduct_mulVec_pos hne
  exact (ne_of_gt hp) hz

 theorem rationalPairing_perfect (A : Matrix n n ℤ) (hs : A.transpose=A)
    (hA : (rationalMatrix A).PosDef) : (rationalPairing A).IsPerfPair := by
  apply LinearMap.IsPerfPair.of_injective (rationalPairing_injective A hA)
  intro x y h
  apply rationalPairing_injective A hA
  apply LinearMap.ext
  intro z
  have he := DFunLike.congr_fun h z
  change rationalPairing A z x=rationalPairing A z y at he
  simpa only [rational_symmetric A hs z x,rational_symmetric A hs z y] using he

end SymmetricSubgroupAsymptotics.CFSGIntegerMatrixPairing
