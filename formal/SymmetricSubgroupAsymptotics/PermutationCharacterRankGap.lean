import SymmetricSubgroupAsymptotics.PermutationTwoGroupRank

/-!
# A local rank gap on the original invariant points

Restriction to an invariant set uses its literal image. The kernel of that
same restriction acts faithfully on the original complement, so the proved
half-degree bound on the kernel preserves any additive gap in the image.
No equality classification or subgroup-rank monotonicity is used.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PermutationCharacterRankSplit

variable {G X : Type} [Group G] [Finite G] [Finite X]
  [MulAction G X] [FaithfulSMul G X]

/-- A proved gap on the literal restriction image remains a gap for the
complete original group. Floors make all parity cases valid, including
an empty complement; S need not itself be one orbit. -/
theorem binary_rank_add_gap_le_half (S : SubMulAction G X)
    (hG : IsPGroup 2 G) (gap : ℕ)
    (hI : Module.finrank (ZMod 2) (PrimeCharacters 2 (Image S)) + gap ≤
      Nat.card S / 2) :
    Module.finrank (ZMod 2) (PrimeCharacters 2 G) + gap ≤ Nat.card X / 2 := by
  classical
  letI : FaithfulSMul (Kernel S) ↥(Sᶜ) := kernel_complement_faithful S
  have hK := permutationTwoGroup_primeCharacterRank_le (Kernel S) ↥(Sᶜ)
    (kernel_isPGroup S 2 hG)
  have hext := rank_le_image_add_kernel S 2
  have hhalf : Nat.card S / 2 + Nat.card ↥(Sᶜ) / 2 ≤ Nat.card X / 2 := by
    simpa only [card_split S] using
      Nat.add_div_le_add_div (Nat.card S) (Nat.card ↥(Sᶜ)) 2
  omega

/-- A strict local inequality gives the strict complete-group inequality,
without a separate nonempty-set or parity hypothesis. -/
theorem binary_rank_lt_half (S : SubMulAction G X) (hG : IsPGroup 2 G)
    (hI : Module.finrank (ZMod 2) (PrimeCharacters 2 (Image S)) < Nat.card S / 2) :
    Module.finrank (ZMod 2) (PrimeCharacters 2 G) < Nat.card X / 2 := by
  have h := binary_rank_add_gap_le_half S hG 1 (by omega)
  omega

/-- The subtraction formulation has an explicit degree guard, so the
local premise cannot become vacuous through truncated subtraction at 0. -/
theorem binary_rank_le_half_sub_one (S : SubMulAction G X) (hG : IsPGroup 2 G)
    (hS : 2 ≤ Nat.card S)
    (hI : Module.finrank (ZMod 2) (PrimeCharacters 2 (Image S)) ≤ Nat.card S / 2 - 1) :
    Module.finrank (ZMod 2) (PrimeCharacters 2 G) ≤ Nat.card X / 2 - 1 := by
  have h := binary_rank_add_gap_le_half S hG 1 (by omega)
  omega

/-- The same original-group gap in prime-abelianization dimension. -/
theorem binary_abelianization_add_gap_le_half (S : SubMulAction G X)
    (hG : IsPGroup 2 G) (gap : ℕ)
    (hI : Module.finrank (ZMod 2) (PrimeCharacters 2 (Image S)) + gap ≤
      Nat.card S / 2) :
    Module.finrank (ZMod 2) (PrimeAbelianization 2 G) + gap ≤ Nat.card X / 2 := by
  simpa only [PrimeAbelianization, Subspace.dual_finrank_eq] using
    binary_rank_add_gap_le_half S hG gap hI

end SymmetricSubgroupAsymptotics.PermutationCharacterRankSplit

namespace SymmetricSubgroupAsymptotics

/-- In particular this applies to the unchanged original permutation
subgroup and an actual orbit, represented as an invariant subset. -/
theorem permutationTwoGroup_literal_rank_gap
    {X : Type} [Finite X] (J : Subgroup (Equiv.Perm X))
    (hJ : IsPGroup 2 J) (S : SubMulAction J X)
    (hI : Module.finrank (ZMod 2)
      (PrimeCharacters 2 (PermutationCharacterRankSplit.Image S)) + 1 ≤ Nat.card S / 2) :
    Module.finrank (ZMod 2) (PrimeCharacters 2 J) ≤ Nat.card X / 2 - 1 := by
  have h := PermutationCharacterRankSplit.binary_rank_add_gap_le_half S hJ 1 hI
  omega

end SymmetricSubgroupAsymptotics
