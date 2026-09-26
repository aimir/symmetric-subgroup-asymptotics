import SymmetricSubgroupAsymptotics.PrimeRelativeHeadChain
import SymmetricSubgroupAsymptotics.PrimeCharacterSubgroupCapacity

/-! Cardinal consequences of the exact original-ambient normal-head chain.
The existing chain retains its extendible restriction image. These bounds
use the same actual quotient and its actual evaluation surjection. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {A : Type*} [Group A]
variable (B C : Subgroup A) [B.Normal] [C.Normal]
variable (p : ℕ) [Fact p.Prime]

/-- The actual quotient-relative head may be enlarged to the complete
character space of that same quotient. The two original relative heads
still use conjugation by the whole ambient A. -/
theorem primeRelativeHead_chain_le_absolute [Finite A] (hBC : B≤C) :
    Module.finrank (ZMod p) (primeRelativeCharacters p C) ≤
      Module.finrank (ZMod p) (primeRelativeCharacters p B) +
        Module.finrank (ZMod p) (PrimeCharacters p (normalChainQuotient B C)) :=
  (primeRelativeHead_chain_le B C p hBC).trans
    (Nat.add_le_add_left (Submodule.finrank_le _) _)

/-- The original normal-chain map and its literal kernel equivalence give
the actual cardinal chain identity, with no numerical order premise. -/
theorem normalChainQuotient_card_mul [Finite A] (hBC : B≤C) :
    Nat.card (normalChainQuotient B C) * Nat.card B = Nat.card C := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (normalChainMap B C).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      (normalChainMap B C) (normalChainMap_surjective B C)).toEquiv,
    Nat.card_congr (normalChainKernelEquiv B C hBC).toEquiv] at h
  exact h.symm

/-- The quotient contribution consumes at most the cardinality of the
same original quotient, by its onto prime-evaluation map. No p-group
assumption, splitting, or a priori quotient rank bound is required. -/
theorem primeRelativeHead_chain_pow_le_card_mul [Finite A] (hBC : B≤C) :
    p ^ Module.finrank (ZMod p) (primeRelativeCharacters p C) ≤
      p ^ Module.finrank (ZMod p) (primeRelativeCharacters p B) *
        Nat.card (normalChainQuotient B C) := by
  calc
    _ ≤ p ^ (Module.finrank (ZMod p) (primeRelativeCharacters p B) +
        Module.finrank (ZMod p) (PrimeCharacters p (normalChainQuotient B C))) :=
      Nat.pow_le_pow_right (Fact.out : p.Prime).pos
        (primeRelativeHead_chain_le_absolute B C p hBC)
    _ = p ^ Module.finrank (ZMod p) (primeRelativeCharacters p B) *
        p ^ Module.finrank (ZMod p) (PrimeCharacters p (normalChainQuotient B C)) :=
      pow_add _ _ _
    _ ≤ _ := Nat.mul_le_mul_left _
      (primeCharacters_pow_finrank_le_card p (normalChainQuotient B C))

end SymmetricSubgroupAsymptotics
