import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic.Abel

/-! Exact binary interpolation of a constant matrix and its square.
Every bit is used once, so products of these factors have ordinary
multiaffine entries. No finite-field table or root-action premise is added. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.MatrixBinaryAffineFactor
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

def affineFactor (t : R) (A : Matrix ι ι R) : Matrix ι ι R :=
  1+t • (A-1)

theorem affineFactor_zero (A : Matrix ι ι R) : affineFactor 0 A=1 := by
  simp only [affineFactor,zero_smul,add_zero]

theorem affineFactor_one (A : Matrix ι ι R) : affineFactor 1 A=A := by
  simp only [affineFactor,one_smul]
  abel

theorem affineFactor_bool (b : Bool) (A : Matrix ι ι R) :
    affineFactor (if b then 1 else 0) A=if b then A else 1 := by
  cases b <;> simp [affineFactor_zero,affineFactor_one]

theorem affineFactor_mulVec (t : R) (A : Matrix ι ι R) (v : ι → R) :
    (affineFactor t A).mulVec v=v+t • (A.mulVec v-v) := by
  simp only [affineFactor,Matrix.add_mulVec,Matrix.smul_mulVec,
    Matrix.sub_mulVec,Matrix.one_mulVec]

theorem two_bits_power (lo hi : Bool) (A : Matrix ι ι R) :
    affineFactor (if hi then 1 else 0) (A^2)*
      affineFactor (if lo then 1 else 0) A = A^(lo.toNat+2*hi.toNat) := by
  cases lo <;> cases hi <;>
    simp [affineFactor_zero,affineFactor_one,pow_succ,pow_two]

end SymmetricSubgroupAsymptotics.MatrixBinaryAffineFactor
