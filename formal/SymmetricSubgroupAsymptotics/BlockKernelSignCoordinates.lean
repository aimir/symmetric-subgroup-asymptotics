import SymmetricSubgroupAsymptotics.BlockKernelClassBound
import Mathlib.GroupTheory.Perm.Sign

/-!
# Binary signs on the literal block kernel

Restriction of the original block kernel to every literal fibre gives a
permutation coordinate.  Conjugation by the original ambient group transports
these coordinates between fibres and preserves their signs.  Hence, on a
transitive block set, one nontrivial inversion coordinate forces every fibre
sign to be nontrivial.  No direct-product replacement of the block kernel is
used.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

private def binarySignUnitHom : ℤˣ →* Multiplicative (ZMod 2) where
  toFun z := Multiplicative.ofAdd (if z = 1 then 0 else 1)
  map_one' := by decide
  map_mul' z w := by
    rcases Int.units_eq_one_or z with rfl | rfl <;>
      rcases Int.units_eq_one_or w with rfl | rfl <;> decide

/-- Parity of a permutation, written as a binary multiplicative character. -/
def permutationBinarySign (X : Type) [Fintype X] :
    Equiv.Perm X →* Multiplicative (ZMod 2) :=
  binarySignUnitHom.comp Equiv.Perm.sign

@[simp] theorem permutationBinarySign_permCongr
    {X Y : Type} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (g : Equiv.Perm X) :
    permutationBinarySign Y (e.permCongr g) = permutationBinarySign X g := by
  change Multiplicative.ofAdd
      (if Equiv.Perm.sign (e.permCongr g) = 1 then 0 else 1) =
    Multiplicative.ofAdd (if Equiv.Perm.sign g = 1 then 0 else 1)
  rw [Equiv.Perm.sign_permCongr]

namespace OriginalBlockSignCoordinates

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
variable (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)

abbrev Kernel : Subgroup A := OriginalBlockClassBound.Kernel (A := A) (X := X)

/-- The original action element transports one literal fibre to another. -/
def fibreTransport (a : A) (x : X) :
    originalBlockFibre b x ≃ originalBlockFibre b (a • x) where
  toFun ω := ⟨a • ω.1, by rw [hb, ω.2]⟩
  invFun ω := ⟨a⁻¹ • ω.1, by
    rw [hb, ω.2, inv_smul_smul]⟩
  left_inv ω := Subtype.ext (inv_smul_smul a ω.1)
  right_inv ω := Subtype.ext (smul_inv_smul a ω.1)

/-- The binary inversion character on one actual fibre coordinate of the
original block kernel. -/
def coordinateSign [∀ x : X, Fintype (originalBlockFibre b x)] (x : X) :
    Kernel (A := A) (X := X) →* Multiplicative (ZMod 2) :=
  (permutationBinarySign (originalBlockFibre b x)).comp
    (OriginalBlockClassBound.coordinate b hb x)

/-- Ambient conjugation transports the whole fibre permutation coordinate. -/
theorem coordinate_conjugation [∀ x : X, Fintype (originalBlockFibre b x)]
    (a : A) (x : X) (k : Kernel (A := A) (X := X)) :
    OriginalBlockClassBound.coordinate b hb (a • x) (MulAut.conjNormal a k) =
      (fibreTransport b hb a x).permCongr
        (OriginalBlockClassBound.coordinate b hb x k) := by
  apply Equiv.ext
  intro ω
  apply Subtype.ext
  change (a * (k : A) * a⁻¹) • ω.1 =
    a • ((k : A) • (a⁻¹ • ω.1))
  simp only [mul_smul]

/-- Consequently the original binary sign is constant under simultaneous
ambient conjugation of the kernel element and transport of the fibre. -/
theorem coordinateSign_conjugation
    [∀ x : X, Fintype (originalBlockFibre b x)]
    (a : A) (x : X) (k : Kernel (A := A) (X := X)) :
    coordinateSign b hb (a • x) (MulAut.conjNormal a k) =
      coordinateSign b hb x k := by
  change permutationBinarySign (originalBlockFibre b (a • x))
      (OriginalBlockClassBound.coordinate b hb (a • x) (MulAut.conjNormal a k)) =
    permutationBinarySign (originalBlockFibre b x)
      (OriginalBlockClassBound.coordinate b hb x k)
  rw [coordinate_conjugation]
  exact permutationBinarySign_permCongr (fibreTransport b hb a x)
    (OriginalBlockClassBound.coordinate b hb x k)

/-- On a transitive original block set, one nontrivial inversion coordinate
forces every literal fibre coordinate to carry a nontrivial binary sign. -/
theorem all_coordinateSigns_nontrivial
    [MulAction.IsPretransitive A X]
    [∀ x : X, Fintype (originalBlockFibre b x)]
    (x₀ : X) (hx₀ : coordinateSign b hb x₀ ≠ 1) :
    ∀ x : X, coordinateSign b hb x ≠ 1 := by
  intro x hx
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq A x₀ x
  apply hx₀
  ext k
  have htransport := coordinateSign_conjugation b hb a x₀ k
  rw [ha, hx, MonoidHom.one_apply] at htransport
  exact htransport.symm

end OriginalBlockSignCoordinates

end SymmetricSubgroupAsymptotics

end
