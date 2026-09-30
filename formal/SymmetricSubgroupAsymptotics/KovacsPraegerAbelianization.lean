import SymmetricSubgroupAsymptotics.EpimorphismKernelLabels
import SymmetricSubgroupAsymptotics.PrimeAbelianization
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.GroupTheory.Abelianization.Defs

/-!
# The Kovács--Praeger abelianization bound as an explicit input

Kovács and Praeger proved that every permutation group of degree `b` has an
abelian quotient of order at most `3^(b/3)`.  It is recorded here as an
explicit hypothesis rather than an axiom.  The consequence used below is
elementary: the binary and ternary character spaces of a finite group jointly
inject into the complex characters of its abelianization.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- Kovács--Praeger, *Finite permutation groups with large abelian
quotients*, Pacific J. Math. 136 (1989), Corollary on p.284 (register entry
LIT-KP): every permutation group of degree `b` has abelianization of order
at most `3^(b/3)`. -/
def KovacsPraegerAbelianizationBound : Prop :=
  ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
    (Nat.card (Abelianization J) : ℝ) ≤ (3 : ℝ) ^ ((b : ℝ) / 3)

/-- Every cyclic character of a finite group factors through its
abelianization and is detected by one complex character there. -/
theorem addMonoidHom_zmod_card_le_abelianization (G : Type*) [Group G] [Finite G]
    (n : ℕ) [NeZero n] :
    Nat.card (Additive G →+ ZMod n) ≤ Nat.card (Abelianization G) := by
  letI : Fintype (Abelianization G) := Fintype.ofFinite _
  let e : (Additive G →+ ZMod n) ≃ (Additive (Abelianization G) →+ ZMod n) :=
    AddMonoidHom.toMultiplicativeRight.trans
      (Abelianization.lift.trans AddMonoidHom.toMultiplicativeRight.symm)
  let χ : (Additive (Abelianization G) →+ ZMod n) → AddChar (Additive (Abelianization G)) ℂ :=
    fun f => ZMod.stdAddChar.compAddMonoidHom f
  have hχ : Function.Injective χ := by
    intro f g h
    apply AddMonoidHom.ext
    intro a
    have ha := DFunLike.congr_fun h a
    exact ZMod.injective_stdAddChar ha
  calc
    Nat.card (Additive G →+ ZMod n) =
        Nat.card (Additive (Abelianization G) →+ ZMod n) := Nat.card_congr e
    _ ≤ Nat.card (AddChar (Additive (Abelianization G)) ℂ) :=
        Nat.card_le_card_of_injective χ hχ
    _ = Nat.card (Abelianization G) := by
        rw [Nat.card_eq_fintype_card, AddChar.card_eq, ← Nat.card_eq_fintype_card]
        exact Nat.card_congr Additive.toMul

/-- The binary and ternary character spaces jointly inject into the sixfold
characters, hence into the complex characters of the abelianization. -/
theorem primeCharacters_two_mul_three_le_abelianization (G : Type*) [Group G]
    [Finite G] :
    Nat.card (PrimeCharacters 2 G) * Nat.card (PrimeCharacters 3 G) ≤
      Nat.card (Abelianization G) := by
  let crt : ZMod (2 * 3) ≃+* ZMod 2 × ZMod 3 := ZMod.chineseRemainder (by norm_num)
  let pair : PrimeCharacters 2 G × PrimeCharacters 3 G → (Additive G →+ ZMod (2 * 3)) :=
    fun fg => crt.symm.toAddMonoidHom.comp (fg.1.prod fg.2)
  letI : Finite (Additive G →+ ZMod (2 * 3)) :=
    Finite.of_injective (fun f : Additive G →+ ZMod (2 * 3) => (f : Additive G → ZMod (2 * 3)))
      DFunLike.coe_injective
  have hpair : Function.Injective pair := by
    intro fg fg' h
    have hx (x : Additive G) : (fg.1 x, fg.2 x) = (fg'.1 x, fg'.2 x) := by
      have h' := DFunLike.congr_fun h x
      exact crt.symm.injective h'
    exact Prod.ext (AddMonoidHom.ext fun x => congrArg Prod.fst (hx x))
      (AddMonoidHom.ext fun x => congrArg Prod.snd (hx x))
  calc
    Nat.card (PrimeCharacters 2 G) * Nat.card (PrimeCharacters 3 G) =
        Nat.card (PrimeCharacters 2 G × PrimeCharacters 3 G) := Nat.card_prod _ _ |>.symm
    _ ≤ Nat.card (Additive G →+ ZMod (2 * 3)) := Nat.card_le_card_of_injective pair hpair
    _ ≤ Nat.card (Abelianization G) := addMonoidHom_zmod_card_le_abelianization G (2 * 3)

/-- Epimorphisms onto a target with jointly injective binary and ternary
characters are bounded by the source abelianization. -/
theorem groupEpimorphism_card_le_abelianization_of_sixfold
    {J Q : Type*} [Group J] [Group Q] [Finite J] [Finite Q]
    (ι₂ : Q →* Multiplicative (ZMod 2)) (ι₃ : Q →* Multiplicative (ZMod 3))
    (hι : ∀ x : Q, ι₂ x = 1 → ι₃ x = 1 → x = 1) :
    Nat.card (GroupEpimorphism J Q) ≤ Nat.card (Abelianization J) := by
  let char : GroupEpimorphism J Q → PrimeCharacters 2 J × PrimeCharacters 3 J :=
    fun f => (AddMonoidHom.toMultiplicativeRight.symm (ι₂.comp f.1),
      AddMonoidHom.toMultiplicativeRight.symm (ι₃.comp f.1))
  have hchar : Function.Injective char := by
    intro f g h
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    have h2 := DFunLike.congr_fun (congrArg Prod.fst h) (Additive.ofMul x)
    have h3 := DFunLike.congr_fun (congrArg Prod.snd h) (Additive.ofMul x)
    change (ι₂ (f.1 x)).toAdd = (ι₂ (g.1 x)).toAdd at h2
    change (ι₃ (f.1 x)).toAdd = (ι₃ (g.1 x)).toAdd at h3
    have hq := hι ((f.1 x)⁻¹ * g.1 x)
      (by rw [map_mul, map_inv, ← Multiplicative.toAdd.injective h2, inv_mul_cancel])
      (by rw [map_mul, map_inv, ← Multiplicative.toAdd.injective h3, inv_mul_cancel])
    exact (inv_mul_eq_one.mp hq)
  calc
    Nat.card (GroupEpimorphism J Q) ≤
        Nat.card (PrimeCharacters 2 J × PrimeCharacters 3 J) :=
      Nat.card_le_card_of_injective char hchar
    _ = Nat.card (PrimeCharacters 2 J) * Nat.card (PrimeCharacters 3 J) := Nat.card_prod _ _
    _ ≤ Nat.card (Abelianization J) := primeCharacters_two_mul_three_le_abelianization J

/-- Under the Kovács--Praeger input, sixfold-detected targets obey the
`3^(b/3)` epimorphism bound on every literal source. -/
theorem groupEpimorphism_card_le_of_kovacsPraeger
    (hKP : KovacsPraegerAbelianizationBound)
    {Q : Type*} [Group Q] [Finite Q]
    (ι₂ : Q →* Multiplicative (ZMod 2)) (ι₃ : Q →* Multiplicative (ZMod 3))
    (hι : ∀ x : Q, ι₂ x = 1 → ι₃ x = 1 → x = 1)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤ (3 : ℝ) ^ ((b : ℝ) / 3) := by
  have h := groupEpimorphism_card_le_abelianization_of_sixfold (J := J) ι₂ ι₃ hι
  exact (Nat.cast_le.mpr h).trans (hKP b J)

end SymmetricSubgroupAsymptotics

end
