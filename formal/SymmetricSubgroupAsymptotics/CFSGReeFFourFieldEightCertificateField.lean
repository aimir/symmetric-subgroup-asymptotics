import Mathlib.Algebra.Field.MinimalAxioms
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.DeriveFintype

/-! A tiny explicit certificate field for the selected Ree F4(8) word.
The polynomial-basis encoding is F2[T]/(T^3+T+1). Only the eight field
elements and the minimal field laws are checked; no group is enumerated. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightCertificateField

structure Element where
  bits : Fin 8
  deriving DecidableEq, Fintype

def ofBits (i : Fin 8) : Element := ⟨i⟩

private def reduce (n : ℕ) : Element := ⟨⟨n%8,Nat.mod_lt _ (by decide)⟩⟩
private def twice (a : ℕ) : ℕ := if a < 4 then 2*a else Nat.xor (2*a) 11
private def mulAux : ℕ → ℕ → ℕ → ℕ
  | 0,_,_ => 0
  | n+1,a,b => Nat.xor (if b%2=1 then a else 0) (mulAux n (twice a) (b/2))
private def rawMul (a b : Element) : Element := reduce (mulAux 3 a.bits.val b.bits.val)
private def rawInv (a : Element) : Element :=
  let a2 := rawMul a a
  rawMul (rawMul a2 a2) a2

private instance zero : Zero Element := ⟨ofBits 0⟩
private instance one : One Element := ⟨ofBits 1⟩
private instance add : Add Element := ⟨fun a b => reduce (Nat.xor a.bits.val b.bits.val)⟩
private instance mul : Mul Element := ⟨rawMul⟩
private instance neg : Neg Element := ⟨fun a => a⟩
private instance inv : Inv Element := ⟨rawInv⟩

instance field : Field Element := Field.ofMinimalAxioms Element
  (by decide +kernel)
  (by decide +kernel)
  (by decide +kernel)
  (by decide +kernel)
  (by decide +kernel)
  (by decide +kernel)
  (by decide +kernel)
  (by decide +kernel)
  (by decide +kernel)
  (by exact ⟨0,1,by decide +kernel⟩)

instance charTwo : CharP Element 2 :=
  (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by decide +kernel)

theorem card : Nat.card Element = 8 := by
  simpa only [Nat.card_eq_fintype_card] using
    (show Fintype.card Element = 8 from by decide +kernel)

def generator : Element := ofBits 2

theorem generator_cubic : generator^3+generator+1 = 0 := by decide +kernel

theorem generator_ne_zero : generator ≠ 0 := by decide +kernel

theorem generator_ne_one : generator ≠ 1 := by decide +kernel

end SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightCertificateField
