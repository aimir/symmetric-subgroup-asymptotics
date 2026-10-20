import SymmetricSubgroupAsymptotics.PrimeRelativeHeadChain
import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalPresentation

/-! Equality in the actual normal-head filtration retains the extension
obstruction. Every relative character of the intersection then extends,
so mixed commutators with the original top-image normal lie in the
intersection's own whole-ambient radical. -/
set_option autoImplicit false
noncomputable section
open scoped Classical commutatorElement

namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G] (p : ℕ) [Fact p.Prime]
  (B N : Subgroup G) [B.Normal] [N.Normal] (hBN : B ≤ N)

include hBN

theorem relativeRadical_inf_le_of_chainRestriction_surjective
    (hsurj : Function.Surjective (normalChainRestriction B N p hBN)) :
    B ⊓ primeRelativeRadical p N ≤ primeRelativeRadical p B := by
  intro x hx
  apply (mem_primeRelativeRadical_iff p B x).mpr
  refine ⟨hx.1, ?_⟩
  intro chi
  obtain ⟨psi, rfl⟩ := hsurj chi
  have hv := ((mem_primeRelativeRadical_iff p N x).mp hx.2).2
  exact hv (normalChainSourceCharactersEquiv N p psi)

theorem chainRestriction_surjective_of_head_additivity [Finite G]
    (heq : Module.finrank (ZMod p) (primeRelativeCharacters p N) =
      Module.finrank (ZMod p) (primeRelativeCharacters p B) +
        Module.finrank (ZMod p) (primeRelativeCharacters p (normalChainQuotient B N))) :
    Function.Surjective (normalChainRestriction B N p hBN) := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  change Module.finrank (ZMod p) (normalChainRetainedCharacters B N p hBN) = _
  have hh := primeRelativeHead_chain_eq B N p hBN
  omega

/-- Exact additive head use forces the original mixed commutators into
the smaller actual intersection radical. No splitting is asserted. -/
theorem mixed_commutator_le_intersection_radical_of_head_additivity
    [Finite G] (K : Subgroup G) [K.Normal]
    (hB : B = N ⊓ K)
    (heq : Module.finrank (ZMod p) (primeRelativeCharacters p N) =
      Module.finrank (ZMod p) (primeRelativeCharacters p B) +
        Module.finrank (ZMod p) (primeRelativeCharacters p (normalChainQuotient B N))) :
    ⁅K, N⁆ ≤ primeRelativeRadical p B := by
  apply (relativeRadical_inf_le_of_chainRestriction_surjective p B N hBN
    (chainRestriction_surjective_of_head_additivity p B N hBN heq)).trans'
  apply le_inf
  · rw [hB]
    exact le_inf (Subgroup.commutator_le_right K N) (Subgroup.commutator_le_left K N)
  · apply Subgroup.commutator_le.mpr
    intro k hk n hn
    have hr := commutator_mem_primeRelativeRadical p N (⟨n, hn⟩ : N) k
    simpa only [commutatorElement_inv] using (primeRelativeRadical p N).inv_mem hr

end SymmetricSubgroupAsymptotics
