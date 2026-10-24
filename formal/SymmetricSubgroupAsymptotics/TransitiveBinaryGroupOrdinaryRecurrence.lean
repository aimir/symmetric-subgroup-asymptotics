import SymmetricSubgroupAsymptotics.BinaryBlockCentralBinomialOrdinaryStep
import SymmetricSubgroupAsymptotics.TraceyAffineInducedModuleInput
import SymmetricSubgroupAsymptotics.FiniteGroupBinaryOrderGenerators
import Mathlib.Data.Finite.Perm

/-! An independent ordinary generator bound for actual transitive finite
2-groups. Every binary step is constructed from the SAME original point
stabilizer lattice; its top is the actual inherited quotient-action range.
The prime-group property descends to that range. No Tracey/MN input,
catalogue, supplied chain, or rank certificate is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TransitiveBinaryGroupOrdinaryRecurrence
open BinaryChainCentralBinomialBudget

/-- Genuine binary chains are obtained by prime-index covers in each
actual smaller 2-group. The trivial degree-one base is included. -/
theorem genRank_le_cumulative (k : ℕ) :
    ∀ (X : Type) [Finite X] (J : Subgroup (Equiv.Perm X)),
      MulAction.IsPretransitive J X → IsPGroup 2 J → Nat.card X = 2^k →
        MarkedC4.genRank J ≤ cumulative k := by
  induction k with
  | zero =>
    intro X _ J _ _ hcard
    have horder : Nat.card J ≤ 1 := by
      have hh := Nat.card_le_card_of_injective
        (Subtype.val : J → Equiv.Perm X) Subtype.val_injective
      simpa only [Nat.card_perm, hcard, pow_zero, Nat.factorial_one] using hh
    have hr := FiniteGroupBinaryOrderGenerators.genRank_le_of_card_le_two_pow J 0
      (by simpa only [pow_zero] using horder)
    simpa only [cumulative, Finset.range_zero, Finset.sum_empty] using hr
  | succ k ih =>
    intro X _ J ht hJ hcard
    letI : MulAction.IsPretransitive J X := ht
    have htwo : 1 < Nat.card X := by
      rw [hcard, pow_succ]
      have hp : 0 < 2^k := pow_pos (by decide) _
      omega
    letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp htwo
    let x : X := Classical.arbitrary X
    obtain ⟨D⟩ := transitiveBinaryPairCover_nonempty J hJ x
    have hblocks : Nat.card D.Points = 2^k := by
      have hd := D.degree_product
      rw [hcard, pow_succ] at hd
      omega
    have htop := ih D.Points D.Top D.top_pretransitive (D.top_isPGroup hJ) hblocks
    exact BinaryBlockCentralBinomialOrdinaryStep.genRank_le_cumulative_of_top
      D.frame (fun _ _ => rfl) D.base k hblocks htop

theorem genRank_le_div_sqrt (k : ℕ) (hk : 1 ≤ k)
    (X : Type) [Finite X] (J : Subgroup (Equiv.Perm X))
    (ht : MulAction.IsPretransitive J X) (hJ : IsPGroup 2 J)
    (hcard : Nat.card X = 2^k) :
    (MarkedC4.genRank J : ℝ) ≤ (2 : ℝ)^k / Real.sqrt k :=
  (show (MarkedC4.genRank J : ℝ) ≤ cumulative k by
    exact_mod_cast genRank_le_cumulative k X J ht hJ hcard).trans
      (cumulative_le_div_sqrt k hk)

/-- This is the existing coarse numerical ceiling, proved here for the
literal transitive 2-group without taking its published INPUT as a premise. -/
theorem genRank_le_traceyCeiling (k : ℕ)
    (X : Type) [Finite X] (J : Subgroup (Equiv.Perm X))
    (ht : MulAction.IsPretransitive J X) (hJ : IsPGroup 2 J)
    (hcard : Nat.card X = 2^k) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  by_cases hk : k = 0
  · have hz : MarkedC4.genRank J = 0 := by
      have hr := genRank_le_cumulative k X J ht hJ hcard
      simpa only [hk, cumulative, Finset.range_zero, Finset.sum_empty, Nat.le_zero] using hr
    rw [hz]
    exact Nat.zero_le _
  · have hr := genRank_le_div_sqrt k (by omega) X J ht hJ hcard
    have hl : Real.logb 2 ((2 : ℝ)^k) = (k : ℝ) := by
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
    have hh := hr.trans (Nat.le_ceil ((2 : ℝ)^k / Real.sqrt k))
    have hc : (MarkedC4.genRank J : ℝ) ≤
        (traceyPermutationGeneratorCeiling (Nat.card X) : ℕ) := by
      simpa only [traceyPermutationGeneratorCeiling, hcard, Nat.cast_pow,
        Nat.cast_ofNat, hl] using hh
    exact_mod_cast hc

/-- Actual finite generators in the original permutation subgroup. -/
theorem exists_generating_finset (k : ℕ)
    (X : Type) [Finite X] (J : Subgroup (Equiv.Perm X))
    (ht : MulAction.IsPretransitive J X) (hJ : IsPGroup 2 J)
    (hcard : Nat.card X = 2^k) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧
      S.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨S, hcardS, hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨S, hgen, hcardS.le.trans (genRank_le_traceyCeiling k X J ht hJ hcard)⟩

/-- The original transitive orbit proves the degree is a power of two;
the caller supplies no exponent or binary-chain certificate. -/
theorem exists_generating_finset_of_two_group
    (X : Type) [Finite X] [Nonempty X] (J : Subgroup (Equiv.Perm X))
    (ht : MulAction.IsPretransitive J X) (hJ : IsPGroup 2 J) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧
      S.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : MulAction.IsPretransitive J X := ht
  let x : X := Classical.arbitrary X
  obtain ⟨k, hk⟩ := hJ.card_orbit x
  have hcard : Nat.card X = 2^k := by
    simpa only [MulAction.orbit_eq_univ J x, Nat.card_univ] using hk
  exact exists_generating_finset k X J ht hJ hcard

/-- Literal degree-n interface for the independent pure binary branch of
the retained coarse Tracey statement. -/
theorem subgroup_exists_generating_finset (n : ℕ) (hn : 2 ≤ n)
    (J : Subgroup (Equiv.Perm (Fin n)))
    (ht : MulAction.IsPretransitive J (Fin n)) (hJ : IsPGroup 2 J) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧
      S.card ≤ traceyPermutationGeneratorCeiling n := by
  letI : NeZero n := ⟨by omega⟩
  simpa only [Nat.card_fin] using exists_generating_finset_of_two_group (Fin n) J ht hJ

end SymmetricSubgroupAsymptotics.TransitiveBinaryGroupOrdinaryRecurrence
