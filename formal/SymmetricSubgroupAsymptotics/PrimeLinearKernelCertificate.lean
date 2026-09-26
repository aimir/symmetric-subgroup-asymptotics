import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness

/-! Finite decoders certify the kernel of an actual linear map. Only
kernel vectors must be recovered; selected vectors need not be distinct
or lie in the kernel. The same interface applies to simultaneous tests
by taking a product-valued linear map. No matrix-to-group identification
or numerical rank is assumed. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
    {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod p) V] [Module (ZMod p) W] [Finite V]

/-- Recovery on the complete actual kernel gives a cardinality upper
bound. No completeness claim about a separately supplied list is used. -/
theorem primeLinearMap_card_ker_le_of_decoder (f : V →ₗ[ZMod p] W)
    (k : ℕ) (select : Fin k → V) (code : V → Fin k)
    (hcover : ∀ x, f x = 0 → select (code x) = x) :
    Nat.card f.ker ≤ k := by
  have hinj : Function.Injective (fun x : f.ker => code (x : V)) := by
    intro x y he
    apply Subtype.ext
    exact (hcover (x : V) x.2).symm.trans
      ((congrArg select he).trans (hcover (y : V) y.2))
  simpa only [Nat.card_fin] using
    Nat.card_le_card_of_injective (fun x : f.ker => code (x : V)) hinj

/-- Actual finite kernel cardinality is a power of the scalar prime. -/
theorem primeLinearMap_card_ker (f : V →ₗ[ZMod p] W) :
    Nat.card f.ker = p ^ Module.finrank (ZMod p) f.ker := by
  simpa only [Nat.card_zmod] using
    (Module.natCard_eq_pow_finrank (K := ZMod p) (V := f.ker))

/-- A finite cardinal bound decodes directly into kernel dimension,
without normalizing a symbolic matrix rank expression. -/
theorem primeLinearMap_finrank_ker_le_of_card_le (f : V →ₗ[ZMod p] W)
    (r : ℕ) (hcard : Nat.card f.ker ≤ p ^ r) :
    Module.finrank (ZMod p) f.ker ≤ r := by
  rw [primeLinearMap_card_ker p f] at hcard
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hcard

/-- Exact cardinality may be used when exact dimension is needed;
an upper cardinal bound alone supplies only an upper dimension bound. -/
theorem primeLinearMap_finrank_ker_eq_of_card_eq (f : V →ₗ[ZMod p] W)
    (r : ℕ) (hcard : Nat.card f.ker = p ^ r) :
    Module.finrank (ZMod p) f.ker = r := by
  rw [primeLinearMap_card_ker p f] at hcard
  exact (Nat.pow_right_injective (Fact.out : p.Prime).one_lt) hcard

/-- A kernel decoder with p^r labels proves the desired dimension
bound for one map or any finite collection of stacked tests. -/
theorem primeLinearMap_finrank_ker_le_of_decoder (f : V →ₗ[ZMod p] W)
    (r : ℕ) (select : Fin (p ^ r) → V) (code : V → Fin (p ^ r))
    (hcover : ∀ x, f x = 0 → select (code x) = x) :
    Module.finrank (ZMod p) f.ker ≤ r :=
  primeLinearMap_finrank_ker_le_of_card_le p f r
    (primeLinearMap_card_ker_le_of_decoder p f (p ^ r) select code hcover)

end SymmetricSubgroupAsymptotics
