import SymmetricSubgroupAsymptotics.BinaryRowCharacters
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Pi

/-!
# Shared word-parity certificates for all binary characters

One original-generator parity vector per row suffices for every character
assignment. Only the coordinate-wise parent equations are checked; the
linear pairing below proves all assignment-specific parent equations at
once. Neither a Frattini-rank assertion nor a declared order is required.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics

variable {G Code : Type*} [Group G] {d n : ℕ}
    {generators : Fin d → G} {E : GeneratorEncoding generators Code}

/-- A checked original-generator parity vector on each actual Cayley row. -/
structure BinaryWordParity (C : EncodedCayleyCertificate E n) where
  parity : Fin n → Fin d → ZMod 2
  identity_eq : ∀ j, parity C.identity j = 0
  parent_eq : ∀ i hi j, parity i j = parity (C.parent i hi) j +
    if j = C.letter i hi then 1 else 0

namespace BinaryWordParity

variable (C : EncodedCayleyCertificate E n) (P : BinaryWordParity C)

def pairing (bits : Fin d → Bool) (v : Fin d → ZMod 2) : ZMod 2 :=
  ∑ j, (if bits j then 0 else 1) * v j

def values (bits : Fin d → Bool) (i : Fin n) : Bool :=
  decide (pairing bits (P.parity i) = 0)

private theorem value_add_bit : ∀ (x : ZMod 2) (b : Bool),
    decide (x + (if b then 0 else 1) = 0) = (decide (x = 0) == b) := by decide

private theorem pairing_parent (bits : Fin d → Bool) (i : Fin n) (hi : i ≠ C.identity) :
    pairing bits (P.parity i) = pairing bits (P.parity (C.parent i hi)) +
      if bits (C.letter i hi) then 0 else 1 := by
  unfold pairing
  simp only [P.parent_eq i hi, mul_add, Finset.sum_add_distrib]
  congr 1
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- All binary character assignments are certified by the same linear
parity-vector parent checks. -/
def characters : BinaryRowCharacters C where
  values := P.values
  identity_eq := by
    intro bits
    simp only [values, pairing, P.identity_eq, mul_zero, Finset.sum_const_zero,
      decide_true]
  parent_eq := by
    intro bits i hi
    unfold values
    rw [P.pairing_parent C bits i hi]
    exact value_add_bit _ _

end BinaryWordParity
end SymmetricSubgroupAsymptotics
