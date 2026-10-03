import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveAcceptedCells
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveSmallCatalogueAccepted
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveSmallLargePrime

/-!
# Exhaustion of the four small affine block-count tables

The numerical source constructors are selected from the literal factorization
of the actual number of blocks.  A factor `5`, `7`, `3^2`, a sufficiently
large binary valuation, or a prime at least eleven gives a uniform source.
The complementary divisor is bounded, so Lean checks the remaining accepted
cells and returns exactly the finite exceptional list from the manuscript.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- The exact positive valuation attached to a prime divisor. -/
structure ExactPrimaryDivisor (s q : ℕ) where
  e : ℕ
  one_le : 1 ≤ e
  pow_dvd : q ^ e ∣ s
  pow_succ_not_dvd : ¬ q ^ (e + 1) ∣ s

noncomputable def ExactPrimaryDivisor.ofPrimeDvd
    {s q : ℕ} (hs : s ≠ 0) (hq : q.Prime) (hdiv : q ∣ s) :
    ExactPrimaryDivisor s q where
  e := s.factorization q
  one_le := hq.factorization_pos_of_dvd hs hdiv
  pow_dvd := by
    exact (hq.pow_dvd_iff_le_factorization hs).mpr le_rfl
  pow_succ_not_dvd := by
    simpa only [Nat.succ_eq_add_one] using
      Nat.pow_succ_factorization_not_dvd hs hq

/-- If no prime at least eleven divides `s`, neither five nor seven divides
it, and its binary and ternary valuations are bounded, then `s` divides the
displayed finite `2^a 3` complement. -/
theorem dvd_binary_ternary_complement
    {s a : ℕ} (hs : s ≠ 0) (ha : 1 ≤ a)
    (hlarge : ¬ ∃ q : ℕ, q.Prime ∧ q ∣ s ∧ 11 ≤ q)
    (h5 : ¬ 5 ∣ s) (h7 : ¬ 7 ∣ s)
    (h9 : ¬ 9 ∣ s) (h2 : ¬ 2 ^ a ∣ s) :
    s ∣ 2 ^ (a - 1) * 3 := by
  rw [← Nat.factorization_le_iff_dvd hs (by positivity)]
  intro p
  by_cases hp : p.Prime
  · by_cases hps : p ∣ s
    · have hp11 : p < 11 := by
        by_contra h
        exact hlarge ⟨p, hp, hps, by omega⟩
      have hpne5 : p ≠ 5 := by
        intro h
        subst p
        exact h5 hps
      have hpne7 : p ≠ 7 := by
        intro h
        subst p
        exact h7 hps
      have hpne4 : p ≠ 4 := by intro h; subst p; norm_num at hp
      have hpne6 : p ≠ 6 := by intro h; subst p; norm_num at hp
      have hpne8 : p ≠ 8 := by intro h; subst p; norm_num at hp
      have hpne9 : p ≠ 9 := by intro h; subst p; norm_num at hp
      have hpne10 : p ≠ 10 := by intro h; subst p; norm_num at hp
      have hp23 : p = 2 ∨ p = 3 := by
        have hp2 := hp.two_le
        omega
      rcases hp23 with rfl | rfl
      · have hv : s.factorization 2 < a := by
          rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hs] at h2
          omega
        rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) (by norm_num),
          Nat.factorization_pow]
        change s.factorization 2 ≤
          (a - 1) * (Nat.factorization 2) 2 + (Nat.factorization 3) 2
        rw [Nat.Prime.factorization_self Nat.prime_two,
          Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)]
        simp
        omega
      · have hv : s.factorization 3 < 2 := by
          have h9' : ¬ 3 ^ 2 ∣ s := by norm_num at h9 ⊢; exact h9
          rw [Nat.Prime.pow_dvd_iff_le_factorization
            (by norm_num : Nat.Prime 3) hs] at h9'
          omega
        rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) (by norm_num),
          Nat.factorization_pow]
        change s.factorization 3 ≤
          (a - 1) * (Nat.factorization 2) 3 + (Nat.factorization 3) 3
        rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2),
          Nat.Prime.factorization_self (by norm_num : Nat.Prime 3)]
        simp
        omega
    · rw [Nat.factorization_eq_zero_of_not_dvd hps]
      exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

/-- The thirteen cells deliberately left to the finite affine-frame
consumers. -/
def IsSmallAffineExceptionalCell (r s : ℕ) : Prop :=
  (r = 5 ∧ (s = 2 ∨ s = 3 ∨ s = 4)) ∨
  (r = 8 ∧ (s = 2 ∨ s = 4 ∨ s = 6)) ∨
  (r = 9 ∧ (s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 6 ∨ s = 12)) ∨
  (r = 16 ∧ (s = 2 ∨ s = 4))

namespace ComponentSource

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
  (hTraceyLog : TraceyAffineInducedModuleInput)
  (hTraceyRefined : TraceyRefinedInducedModuleInput)
  (hTraceyPerm : TraceyPermutationGeneratorInput)
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)

private abbrev blocks := Nat.card block.Points

private theorem blocks_ne_zero : blocks block ≠ 0 :=
  (Nat.card_pos (α := block.Points)).ne'

private theorem valuation_ge_of_pow_dvd
    {q d : ℕ} (hq : q.Prime) (hpow : q ^ d ∣ blocks block) :
    d ≤ (blocks block).factorization q := by
  exact (hq.pow_dvd_iff_le_factorization (blocks_ne_zero block)).mp hpow

/-- Degree five: every block count is accepted except `2,3,4`. -/
noncomputable def degreeFiveExhaustion
    (hr : Nat.card block.Fibre = 5) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P ⊕
      PLift (blocks block = 2 ∨ blocks block = 3 ∨ blocks block = 4) := by
  by_cases h5 : 5 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      (by norm_num : Nat.Prime 5) h5
    exact .inl (of_degreeFive_primeFive hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr E.e E.one_le E.pow_dvd E.pow_succ_not_dvd)
  by_cases h7 : 7 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      (by norm_num : Nat.Prime 7) h7
    exact .inl (of_degreeFive_primeSeven hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr E.e E.one_le E.pow_dvd E.pow_succ_not_dvd)
  by_cases h9 : 9 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      (by norm_num : Nat.Prime 3) (dvd_trans (by norm_num : 3 ∣ 9) h9)
    have he : 2 ≤ E.e := by
      simpa only [E, ExactPrimaryDivisor.ofPrimeDvd] using
        (valuation_ge_of_pow_dvd block (by norm_num : Nat.Prime 3)
          (by norm_num at h9 ⊢; exact h9))
    exact .inl (of_degreeFive_primeThree hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr E.e he E.pow_dvd E.pow_succ_not_dvd)
  by_cases h32 : 2 ^ 5 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      Nat.prime_two (dvd_trans (by norm_num : 2 ∣ 2 ^ 5) h32)
    have he : 5 ≤ E.e := by
      simpa only [E, ExactPrimaryDivisor.ofPrimeDvd] using
        (valuation_ge_of_pow_dvd block Nat.prime_two h32)
    exact .inl (of_degreeFive_primeTwo hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr E.e he E.pow_dvd E.pow_succ_not_dvd)
  by_cases h6 : 6 ∣ blocks block
  · exact .inl (of_degreeFive_even_threePrimary hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm block P hr
        (dvd_trans (by norm_num : 3 ∣ 6) h6) h9
        (even_iff_two_dvd.mpr (dvd_trans (by norm_num : 2 ∣ 6) h6)))
  by_cases hlarge : ∃ q : ℕ, q.Prime ∧ q ∣ blocks block ∧ 11 ≤ q
  · let q := Classical.choose hlarge
    have hqdata := Classical.choose_spec hlarge
    let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      hqdata.1 hqdata.2.1
    exact .inl (of_degreeFive_largePrime hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr q E.e hqdata.1 hqdata.2.2 E.one_le E.pow_dvd
        E.pow_succ_not_dvd)
  have hdvd : blocks block ∣ 48 := by
    simpa using dvd_binary_ternary_complement (blocks_ne_zero block)
      (by norm_num) hlarge h5 h7 h9 h32
  have hs2 : 2 ≤ blocks block := block.degrees_ge_two.2
  have hs48 : blocks block ≤ 48 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases hs : blocks block
  all_goals norm_num at hdvd
  all_goals norm_num at h6
  all_goals first
    | exact .inl (of_degreeFive_eightBlocks hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P hr hs)
    | exact .inl (of_degreeFive_sixteenBlocks hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P hr hs)
    | exact .inr ⟨by simp [hs]⟩

/-- Degree eight: every block count is accepted except `2,4,6`. -/
noncomputable def degreeEightExhaustion
    (D : PublishedPrimitiveAffineSmallCatalogueData)
    (hr : Nat.card block.Fibre = 8) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P ⊕
      PLift (blocks block = 2 ∨ blocks block = 4 ∨ blocks block = 6) := by
  by_cases h5 : 5 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      (by norm_num : Nat.Prime 5) h5
    exact .inl (of_degreeEight_primeFive hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr E.e E.one_le E.pow_dvd E.pow_succ_not_dvd)
  by_cases h7 : 7 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      (by norm_num : Nat.Prime 7) h7
    exact .inl (of_degreeEight_primeSeven hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr E.e E.one_le E.pow_dvd E.pow_succ_not_dvd)
  by_cases h9 : 9 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      (by norm_num : Nat.Prime 3) (dvd_trans (by norm_num : 3 ∣ 9) h9)
    have he : 2 ≤ E.e := by
      simpa only [E, ExactPrimaryDivisor.ofPrimeDvd] using
        (valuation_ge_of_pow_dvd block (by norm_num : Nat.Prime 3)
          (by norm_num at h9 ⊢; exact h9))
    exact .inl (of_degreeEight_primeThree hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr E.e he E.pow_dvd E.pow_succ_not_dvd)
  by_cases h8 : 2 ^ 3 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      Nat.prime_two (dvd_trans (by norm_num : 2 ∣ 2 ^ 3) h8)
    have he : 3 ≤ E.e := by
      simpa only [E, ExactPrimaryDivisor.ofPrimeDvd] using
        (valuation_ge_of_pow_dvd block Nat.prime_two h8)
    exact .inl (of_degreeEight_primeTwo hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P D hr E.e he E.pow_dvd E.pow_succ_not_dvd)
  by_cases hlarge : ∃ q : ℕ, q.Prime ∧ q ∣ blocks block ∧ 11 ≤ q
  · let q := Classical.choose hlarge
    have hqdata := Classical.choose_spec hlarge
    let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      hqdata.1 hqdata.2.1
    exact .inl (of_degreeEight_largePrime hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr q E.e hqdata.1 hqdata.2.2 E.one_le E.pow_dvd
        E.pow_succ_not_dvd)
  have hdvd : blocks block ∣ 12 := by
    simpa using dvd_binary_ternary_complement (blocks_ne_zero block)
      (by norm_num) hlarge h5 h7 h9 h8
  have hs2 : 2 ≤ blocks block := block.degrees_ge_two.2
  have hs12 : blocks block ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases hs : blocks block
  all_goals norm_num at hdvd
  all_goals first
    | exact .inl (of_degreeEight_threeBlocks hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P D hr hs)
    | exact .inl (of_degreeEight_twelveBlocks hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P D hr hs)
    | exact .inr ⟨by simp [hs]⟩

/-- Degree nine: every block count is accepted except `2,3,4,6,12`. -/
noncomputable def degreeNineExhaustion
    (hr : Nat.card block.Fibre = 9) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P ⊕
      PLift (blocks block = 2 ∨ blocks block = 3 ∨ blocks block = 4 ∨
        blocks block = 6 ∨ blocks block = 12) := by
  by_cases h5 : 5 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      (by norm_num : Nat.Prime 5) h5
    exact .inl (of_degreeNine_primeFive hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr E.e E.one_le E.pow_dvd E.pow_succ_not_dvd)
  by_cases h7 : 7 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      (by norm_num : Nat.Prime 7) h7
    exact .inl (of_degreeNine_primeSeven hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr E.e E.one_le E.pow_dvd E.pow_succ_not_dvd)
  by_cases h9 : 9 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      (by norm_num : Nat.Prime 3) (dvd_trans (by norm_num : 3 ∣ 9) h9)
    have he : 2 ≤ E.e := by
      simpa only [E, ExactPrimaryDivisor.ofPrimeDvd] using
        (valuation_ge_of_pow_dvd block (by norm_num : Nat.Prime 3)
          (by norm_num at h9 ⊢; exact h9))
    exact .inl (of_degreeNine_primeThree hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr E.e he E.pow_dvd E.pow_succ_not_dvd)
  by_cases h16 : 2 ^ 4 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      Nat.prime_two (dvd_trans (by norm_num : 2 ∣ 2 ^ 4) h16)
    have he : 4 ≤ E.e := by
      simpa only [E, ExactPrimaryDivisor.ofPrimeDvd] using
        (valuation_ge_of_pow_dvd block Nat.prime_two h16)
    exact .inl (of_degreeNine_primeTwo hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr E.e he E.pow_dvd E.pow_succ_not_dvd)
  by_cases hlarge : ∃ q : ℕ, q.Prime ∧ q ∣ blocks block ∧ 11 ≤ q
  · let q := Classical.choose hlarge
    have hqdata := Classical.choose_spec hlarge
    let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      hqdata.1 hqdata.2.1
    exact .inl (of_degreeNine_largePrime hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr q E.e hqdata.1 hqdata.2.2 E.one_le E.pow_dvd
        E.pow_succ_not_dvd)
  have hdvd : blocks block ∣ 24 := by
    simpa using dvd_binary_ternary_complement (blocks_ne_zero block)
      (by norm_num) hlarge h5 h7 h9 h16
  have hs2 : 2 ≤ blocks block := block.degrees_ge_two.2
  have hs24 : blocks block ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases hs : blocks block
  all_goals norm_num at hdvd
  all_goals first
    | exact .inl (of_degreeNine_eightBlocks hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P hr hs)
    | exact .inl (of_degreeNine_twentyFourBlocks hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P hr hs)
    | exact .inr ⟨by simp [hs]⟩

/-- Degree sixteen: every block count is accepted except `2,4`. -/
noncomputable def degreeSixteenExhaustion
    (D : PublishedPrimitiveAffineSmallCatalogueData)
    (hr : Nat.card block.Fibre = 16) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P ⊕
      PLift (blocks block = 2 ∨ blocks block = 4) := by
  by_cases h5 : 5 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      (by norm_num : Nat.Prime 5) h5
    exact .inl (of_degreeSixteen_primeFive hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr E.e E.one_le E.pow_dvd E.pow_succ_not_dvd)
  by_cases h7 : 7 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      (by norm_num : Nat.Prime 7) h7
    exact .inl (of_degreeSixteen_primeSeven hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr E.e E.one_le E.pow_dvd E.pow_succ_not_dvd)
  by_cases h9 : 9 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      (by norm_num : Nat.Prime 3) (dvd_trans (by norm_num : 3 ∣ 9) h9)
    have he : 2 ≤ E.e := by
      simpa only [E, ExactPrimaryDivisor.ofPrimeDvd] using
        (valuation_ge_of_pow_dvd block (by norm_num : Nat.Prime 3)
          (by norm_num at h9 ⊢; exact h9))
    exact .inl (of_degreeSixteen_primeThree hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr E.e he E.pow_dvd E.pow_succ_not_dvd)
  by_cases h32 : 2 ^ 5 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      Nat.prime_two (dvd_trans (by norm_num : 2 ∣ 2 ^ 5) h32)
    have he : 5 ≤ E.e := by
      simpa only [E, ExactPrimaryDivisor.ofPrimeDvd] using
        (valuation_ge_of_pow_dvd block Nat.prime_two h32)
    exact .inl (of_degreeSixteen_primeTwo hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P D hr E.e he E.pow_dvd E.pow_succ_not_dvd)
  by_cases hlarge : ∃ q : ℕ, q.Prime ∧ q ∣ blocks block ∧ 11 ≤ q
  · let q := Classical.choose hlarge
    have hqdata := Classical.choose_spec hlarge
    let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      hqdata.1 hqdata.2.1
    exact .inl (of_degreeSixteen_largePrime hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr q E.e hqdata.1 hqdata.2.2 E.one_le E.pow_dvd
        E.pow_succ_not_dvd)
  have hdvd : blocks block ∣ 48 := by
    simpa using dvd_binary_ternary_complement (blocks_ne_zero block)
      (by norm_num) hlarge h5 h7 h9 h32
  have hs2 : 2 ≤ blocks block := block.degrees_ge_two.2
  have hs48 : blocks block ≤ 48 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases hs : blocks block
  all_goals norm_num at hdvd
  all_goals first
    | exact .inl (of_degreeSixteen_threeBlocks hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P D hr hs)
    | exact .inl (of_degreeSixteen_sixBlocks hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P D hr hs)
    | exact .inl (of_degreeSixteen_eightBlocks hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P D hr hs)
    | exact .inl (of_degreeSixteen_twelveBlocks hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P D hr hs)
    | exact .inl (of_degreeSixteen_sixteenBlocks hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P D hr hs)
    | exact .inl (of_degreeSixteen_twentyFourBlocks hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P D hr hs)
    | exact .inl (of_degreeSixteen_fortyEightBlocks hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P D hr hs)
    | exact .inr ⟨by simp [hs]⟩

end ComponentSource
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
