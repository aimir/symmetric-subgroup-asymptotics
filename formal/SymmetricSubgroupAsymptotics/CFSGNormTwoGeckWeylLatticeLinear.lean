import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordAlgebra
import Mathlib.Algebra.Module.Equiv.Basic

/-! The original integral linear automorphism of each literal Weyl word,
with its inverse and preservation of the actual integer Cartan pairing. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylLatticeLinear
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckWeylWordAlgebra
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

def wordLinear : List (Fin r)→((n→ℤ)≃ₗ[ℤ](n→ℤ))
  | []=>1
  | i::w=>(reflectionEquiv A (s i)).toIntLinearEquiv*wordLinear w

theorem wordLinear_root (w : List (Fin r)) (k : Roots A) :
    wordLinear A hs hp b s w k.val=(wordRoot A hs hp b s w k).val := by
  induction w with
  | nil=>rfl
  | cons i w ih=>
    change reflectionEquiv A (s i) (wordLinear A hs hp b s w k.val)=_
    rw [ih]
    rfl

theorem wordLinear_append (v w : List (Fin r)) :
    wordLinear A hs hp b s (v++w)=wordLinear A hs hp b s v*wordLinear A hs hp b s w := by
  induction v with
  | nil=>simp only [List.nil_append,wordLinear,one_mul]
  | cons i v ih=>rw [List.cons_append,wordLinear,ih,wordLinear,mul_assoc]

theorem wordLinear_inverseWord (w : List (Fin r)) :
    wordLinear A hs hp b s (inverseWord w)=(wordLinear A hs hp b s w)⁻¹ := by
  induction w with
  | nil=>simp only [inverseWord,wordLinear,inv_one]
  | cons i w ih=>
    let R : (n→ℤ)≃ₗ[ℤ](n→ℤ) := (reflectionEquiv A (s i)).toIntLinearEquiv
    have hR : R*R=1 := by
      apply LinearEquiv.ext
      intro x
      exact (reflectionEquiv A (s i)).left_inv x
    have hi : R⁻¹=R := inv_eq_of_mul_eq_one_right hR
    rw [inverseWord,wordLinear_append,ih]
    change (wordLinear A hs hp b s w)⁻¹*(R*(R*(R*1)))=
      (R*wordLinear A hs hp b s w)⁻¹
    simp only [mul_one,mul_inv_rev,hi,hR]

theorem wordRoot_integer_pairing (w : List (Fin r)) (j k : Roots A) :
    integerPairing A (wordRoot A hs hp b s w j).val (wordRoot A hs hp b s w k).val=
      integerPairing A j.val k.val := by
  apply (Int.cast_injective : Function.Injective (Int.cast : ℤ→ℚ))
  change (integerPairing A (wordRoot A hs hp b s w j).val
    (wordRoot A hs hp b s w k).val:ℚ)=(integerPairing A j.val k.val:ℚ)
  rw [←pairing_cast,←pairing_cast]
  induction w with
  | nil=>rfl
  | cons i w ih=>
    change (rootPairing A hs hp).pairing
      ((rootPairing A hs hp).reflectionPerm (s i) (wordRoot A hs hp b s w j))
      ((rootPairing A hs hp).reflectionPerm (s i) (wordRoot A hs hp b s w k))=_
    rw [RootPairing.pairing_reflectionPerm,RootPairing.reflectionPerm_self]
    exact ih

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylLatticeLinear
