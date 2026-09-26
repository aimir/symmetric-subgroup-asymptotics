import SymmetricSubgroupAsymptotics.BinaryTransgressionExact
import SymmetricSubgroupAsymptotics.PermutationTwoGroupRank

/-! The actual terminal inflation defect is bounded on the original
faithful permutation action. The rank theorem is applied to the literal
binary-evaluation kernel, with its inherited faithful action. This does
not replace the source by a master inverse image or by its abelianization.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- Whole-group invariant characters of the actual evaluation kernel are
bounded by its absolute characters on the same original point set. -/
theorem terminalRestrictedInflationKernel_permutation_le_half
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (hG : IsPGroup 2 G) :
    Module.finrank (ZMod 2) (terminalRestrictedInflationKernel G) ≤ Nat.card X / 2 := by
  rw [terminalRestrictedInflationKernel_finrank_eq_relativeHead]
  let K := (AddMonoidHom.toMultiplicativeRight (binaryAbelianizationMap G)).ker
  exact (Submodule.finrank_le (primeRelativeCharacters 2 K)).trans
    (permutationTwoGroup_primeCharacterRank_le K X (hG.to_subgroup K))

/-- No fullness, transitivity, or supplied character-rank input is needed. -/
theorem terminalRestrictedInflationKernel_literal_permutation_le_half
    {X : Type} [Finite X] (H : Subgroup (Equiv.Perm X)) (hH : IsPGroup 2 H) :
    Module.finrank (ZMod 2) (terminalRestrictedInflationKernel H) ≤ Nat.card X / 2 :=
  terminalRestrictedInflationKernel_permutation_le_half H X hH

theorem terminalRestrictedInflationKernel_literal_fin_even_le
    (C : ℕ) (H : Subgroup (Equiv.Perm (Fin (2*C)))) (hH : IsPGroup 2 H) :
    Module.finrank (ZMod 2) (terminalRestrictedInflationKernel H) ≤ C := by
  simpa only [Nat.card_fin, Nat.mul_div_cancel_left C (by decide : 0 < 2)] using
    terminalRestrictedInflationKernel_literal_permutation_le_half H hH

end SymmetricSubgroupAsymptotics
