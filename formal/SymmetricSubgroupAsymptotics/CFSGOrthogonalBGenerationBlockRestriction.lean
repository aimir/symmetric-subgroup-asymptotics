import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.Group.Subgroup.Defs

/-! Restriction of actual block units with last row (0,1). This is a
homomorphism on that proved subgroup, not an upper-left-block operation
asserted multiplicative on arbitrary ambient matrices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationBlockRestriction
open Matrix
variable (K : Type*) [CommRing K] (n : Type*) [Fintype n] [DecidableEq n]

abbrev ExtendedMatrix := Matrix (n ⊕ Unit) (n ⊕ Unit) K

def FixedLastRow (A : ExtendedMatrix K n) : Prop :=
  ∀ j, A (Sum.inr ()) j = if j = Sum.inr () then 1 else 0

omit [Fintype n] in
theorem fixedLastRow_one : FixedLastRow K n 1 := by
  intro j
  simp [Matrix.one_apply, eq_comm]

theorem fixedLastRow_mul (A B : ExtendedMatrix K n)
    (hA : FixedLastRow K n A) (hB : FixedLastRow K n B) : FixedLastRow K n (A * B) := by
  intro j
  have hA' (k : n ⊕ Unit) : A (Sum.inr ()) k = if k = Sum.inr () then 1 else 0 := hA k
  simpa [Matrix.mul_apply, hA'] using hB j

theorem fixedLastRow_inv (g : (ExtendedMatrix K n)ˣ)
    (hg : FixedLastRow K n g) : FixedLastRow K n (↑g⁻¹ : ExtendedMatrix K n) := by
  intro j
  have hm : (g : ExtendedMatrix K n) * (↑g⁻¹ : ExtendedMatrix K n) = 1 := Units.mul_inv g
  have hh := congrArg (fun A : ExtendedMatrix K n => A (Sum.inr ()) j) hm
  have hg' (k : n ⊕ Unit) : (g : ExtendedMatrix K n) (Sum.inr ()) k =
      if k = Sum.inr () then 1 else 0 := hg k
  simpa [Matrix.mul_apply, hg', Matrix.one_apply, eq_comm] using hh

def rowSubgroup : Subgroup (ExtendedMatrix K n)ˣ where
  carrier := {g | FixedLastRow K n g}
  one_mem' := fixedLastRow_one K n
  mul_mem' := fun hA hB => fixedLastRow_mul K n _ _ hA hB
  inv_mem' := fun hA => fixedLastRow_inv K n _ hA

def upperBlock (A : ExtendedMatrix K n) : Matrix n n K := A.submatrix Sum.inl Sum.inl

omit [Fintype n] in
theorem upperBlock_one : upperBlock K n 1 = 1 := by
  ext i j
  simp [upperBlock, Matrix.one_apply]

theorem upperBlock_mul (A B : ExtendedMatrix K n) (hB : FixedLastRow K n B) :
    upperBlock K n (A * B) = upperBlock K n A * upperBlock K n B := by
  ext i j
  have hB' : B (Sum.inr ()) (Sum.inl j) = 0 := by simpa using hB (Sum.inl j)
  simp [upperBlock, Matrix.mul_apply, Fintype.sum_sum_type, hB']

def upperBlockUnit (g : rowSubgroup K n) : (Matrix n n K)ˣ where
  val := upperBlock K n (g.val : ExtendedMatrix K n)
  inv := upperBlock K n (↑g.val⁻¹ : ExtendedMatrix K n)
  val_inv := by
    rw [← upperBlock_mul K n _ _ (fixedLastRow_inv K n g.val g.property),
      Units.mul_inv, upperBlock_one]
  inv_val := by
    rw [← upperBlock_mul K n _ _ g.property, Units.inv_mul, upperBlock_one]

def upperBlockHom : rowSubgroup K n →* (Matrix n n K)ˣ where
  toFun := upperBlockUnit K n
  map_one' := Units.ext (upperBlock_one K n)
  map_mul' _g h := Units.ext (upperBlock_mul K n _ _ h.property)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationBlockRestriction
