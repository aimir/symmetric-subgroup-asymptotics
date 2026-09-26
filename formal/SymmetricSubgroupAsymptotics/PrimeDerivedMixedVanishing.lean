import SymmetricSubgroupAsymptotics.PrimeDerivedCrossingCommutator
import SymmetricSubgroupAsymptotics.PrimeRelativeCharacterKernel

/-! The complete original derived characters vanishing on [N,G] are
exactly the parameters annihilating the actual evaluation image of N.
The reverse implication checks literal mixed commutator generators in
the same original character kernel. No pair-radical hypothesis is used. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hker : (primeAbelianizationGroupMap p G).ker = commutator G)

theorem derivedCharactersVanishingOn_mixedCommutator_eq_joint
    (N : Subgroup G) :
    derivedCharactersVanishingOn p ⁅N, (⊤ : Subgroup G)⁆ =
      linearJointAnnihilator (derivedEvaluationBilinearMap p hker)
        (primeDerivedImage p N) := by
  apply le_antisymm (derivedCharactersVanishingOn_mixedCommutator_le_joint p hker N)
  intro χ hχ
  have hM : ⁅N, (⊤ : Subgroup G)⁆ ≤
      primeRelativeCharacterKernel p (commutator G) χ := by
    apply Subgroup.commutator_le.mpr
    intro n hn g _
    apply (coe_mem_primeRelativeCharacterKernel_iff p (commutator G) χ
      (derivedCommutatorElement n g)).mpr
    have hv : primeAbelianizationMap p G (Additive.ofMul n) ∈ primeDerivedImage p N :=
      (mem_primeDerivedImage_iff p N _).mpr ⟨⟨n, hn⟩, rfl⟩
    have hz : derivedEvaluationBilinear p hker χ
        (primeAbelianizationMap p G (Additive.ofMul n)) = 0 := hχ _ hv
    have he := LinearMap.congr_fun hz (primeAbelianizationMap p G (Additive.ofMul g))
    rw [derivedEvaluationBilinear_eval] at he
    exact he
  intro d hd
  exact (coe_mem_primeRelativeCharacterKernel_iff p (commutator G) χ d).mp (hM hd)

end SymmetricSubgroupAsymptotics
