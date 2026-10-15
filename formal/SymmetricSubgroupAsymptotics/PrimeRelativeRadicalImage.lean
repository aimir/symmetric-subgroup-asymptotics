import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalPresentation
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadChain
import Mathlib.GroupTheory.Subgroup.Center

/-! The image of the original normal subgroup in the quotient by its
actual relative-character radical is central, has prime exponent, and
retains the entire original relative head. -/

set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] {G : Type} [Group G]
    (N : Subgroup G) [N.Normal]

theorem primeRelativeRadical_image_le_center :
    normalChainQuotient (primeRelativeRadical p N) N ≤
      Subgroup.center (G ⧸ primeRelativeRadical p N) := by
  rintro _ ⟨n, hn, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (primeRelativeRadical p N) y
  have hc : ⁅QuotientGroup.mk' (primeRelativeRadical p N) n,
      QuotientGroup.mk' (primeRelativeRadical p N) g⁆ = 1 := by
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff (N := primeRelativeRadical p N) _).mpr
      (commutator_mem_primeRelativeRadical p N ⟨n, hn⟩ g)
  exact (commutatorElement_eq_one_iff_mul_comm.mp hc).symm

theorem primeRelativeRadical_image_pow_eq_one
    (a : normalChainQuotient (primeRelativeRadical p N) N) :
    (a : G ⧸ primeRelativeRadical p N) ^ p = 1 := by
  obtain ⟨n, hn, he⟩ := a.2
  rw [← he, ← map_pow]
  exact (QuotientGroup.eq_one_iff (N := primeRelativeRadical p N) _).mpr
    (pow_mem_primeRelativeRadical p N ⟨n, hn⟩)

theorem primeRelativeRadical_restriction_eq_zero :
    normalChainRestriction (primeRelativeRadical p N) N p
      (primeRelativeRadical_le p N) = 0 := by
  ext χ b
  let n : N := ⟨(b : G), primeRelativeRadical_le p N b.2⟩
  have hn : n ∈ primeRelativeRadicalKernel p N :=
    (coe_mem_primeRelativeRadical_iff p N n).mp b.2
  exact (mem_primeRelativeRadicalKernel_iff p N n).mp hn
    (normalChainSourceCharactersEquiv N p χ)

theorem primeRelativeHead_radical_image_eq [Finite G] :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) =
      Module.finrank (ZMod p)
        (primeRelativeCharacters p (normalChainQuotient (primeRelativeRadical p N) N)) := by
  have hz : normalChainRetainedCharacters (primeRelativeRadical p N) N p
      (primeRelativeRadical_le p N) = ⊥ := by
    unfold normalChainRetainedCharacters
    rw [primeRelativeRadical_restriction_eq_zero, LinearMap.range_zero]
  rw [primeRelativeHead_chain_eq (primeRelativeRadical p N) N p
    (primeRelativeRadical_le p N), hz, finrank_bot, add_zero]

end SymmetricSubgroupAsymptotics

end
