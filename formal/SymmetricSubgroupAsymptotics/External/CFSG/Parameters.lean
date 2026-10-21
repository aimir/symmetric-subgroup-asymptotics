import Mathlib.FieldTheory.Finite.GaloisField

namespace CFSG

/-- A specified finite field size p^e, with p prime and e positive. -/
structure PrimePower where
  prime : ℕ
  exponent : ℕ
  prime_isPrime : prime.Prime
  exponent_pos : 0 < exponent

namespace PrimePower
instance (q : PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩

def order (q : PrimePower) : ℕ := q.prime ^ q.exponent
noncomputable abbrev Field (q : PrimePower) := GaloisField q.prime q.exponent

/-- Specified extension field of degree d; only positive d are used below. -/
noncomputable abbrev Extension (q : PrimePower) (d : ℕ) :=
  GaloisField q.prime (d * q.exponent)

theorem card_field (q : PrimePower) : Nat.card q.Field = q.order :=
  GaloisField.card q.prime q.exponent (Nat.ne_of_gt q.exponent_pos)

end PrimePower
end CFSG
