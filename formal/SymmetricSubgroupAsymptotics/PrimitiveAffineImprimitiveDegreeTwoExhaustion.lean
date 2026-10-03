import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveDegreeThreeExhaustion
import SymmetricSubgroupAsymptotics.BinaryZeroCutWideParameters

/-!
# Exact degree-two affine component exhaustion

A primitive affine component on two points has literal order dividing two.
Tracey's retained primary rates therefore accept every block count except

* `2^a` with `1 <= a <= 8`, and
* `3 * 2^a` with `a <= 10`.

These are exactly the pair-frame counts removed by the small, selected and
residual pair sectors.  The pure binary tail uses the exact soluble
central-binomial rate; the mixed tail uses the retained binary valuation.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- From exponent nine onward the exact middle coefficient has density at
most `63/256`.  Equality holds at exponent nine. -/
theorem binary_middle_le_sixtyThree_twoFiftySix
    (e : ℕ) (he : 9 ≤ e) :
    256 * e.choose (e / 2) ≤ 63 * 2 ^ e := by
  induction e, he using Nat.le_induction with
  | base => decide
  | succ e he ih =>
      calc
        256 * (e + 1).choose ((e + 1) / 2) ≤
            256 * (2 * e.choose (e / 2)) :=
          Nat.mul_le_mul_left 256 (binary_middle_succ_le_twice e)
        _ = 2 * (256 * e.choose (e / 2)) := by ring
        _ ≤ 2 * (63 * 2 ^ e) := Nat.mul_le_mul_left 2 ih
        _ = 63 * 2 ^ (e + 1) := by rw [pow_succ]; ring

namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
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

private theorem budget_two_largePrime
    (q e : ℕ) (hq5 : 5 ≤ q) (he : 1 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate (blocks block) q e) 2 ≤
      (1 / 10 : ℝ) * blocks block := by
  rw [refinedWeightedFactorBudget_two]
  have h2 := traceyPrimaryRate_nonmatching_le (blocks block) q e 2 5
    (by omega) (by
      calc 5 ≤ q := hq5
        _ = q ^ 1 := by simp
        _ ≤ q ^ e := Nat.pow_le_pow_right (by omega) he) (by norm_num)
  have h2' : ActualWreathCompressionTower.traceyPrimaryRate
      (blocks block) q e 2 ≤ (blocks block : ℝ) / 5 := by
    norm_num at h2 ⊢
    exact h2
  calc
    _ ≤ (1 / 2 : ℝ) * ((blocks block : ℝ) / 5) := by gcongr
    _ = (1 / 10 : ℝ) * blocks block := by ring

noncomputable def of_degreeTwo_largePrime
    (hr : Nat.card block.Fibre = 2)
    (q e : ℕ) (hq : q.Prime) (hq5 : 5 ≤ q)
    (he : 1 ≤ e) (hdiv : q ^ e ∣ blocks block)
    (hmax : ¬ q ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P q e 2 hq he hdiv hmax (by norm_num)
      (component_card_dvd_2 block P hr)
  apply smallAffine_even_budget_margin 2 (blocks block) w
      (by simpa only [hr] using width_eq block)
      (by
        rw [width_eq block, hr]
        exact ⟨Nat.card block.Points, by ring⟩)
      (1 / 10) _
  · unfold preE7CharacterRho
    norm_num
  · exact budget_two_largePrime block q e hq5 he

private theorem budget_two_ternary_two
    (e : ℕ) (he : 2 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate (blocks block) 3 e) 2 ≤
      (1 / 18 : ℝ) * blocks block := by
  rw [refinedWeightedFactorBudget_two]
  have h2 := traceyPrimaryRate_nonmatching_le (blocks block) 3 e 2 9
    (by norm_num) (Nat.pow_le_pow_right (by norm_num : 0 < 3) he) (by norm_num)
  have h2' : ActualWreathCompressionTower.traceyPrimaryRate
      (blocks block) 3 e 2 ≤ (blocks block : ℝ) / 9 := by
    norm_num at h2 ⊢
    exact h2
  calc
    _ ≤ (1 / 2 : ℝ) * ((blocks block : ℝ) / 9) := by gcongr
    _ = (1 / 18 : ℝ) * blocks block := by ring

noncomputable def of_degreeTwo_ternaryTwo
    (hr : Nat.card block.Fibre = 2)
    (e : ℕ) (he : 2 ≤ e) (hdiv : 3 ^ e ∣ blocks block)
    (hmax : ¬ 3 ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P 3 e 2 (by norm_num) (by omega) hdiv hmax (by norm_num)
      (component_card_dvd_2 block P hr)
  apply smallAffine_even_budget_margin 2 (blocks block) w
      (by simpa only [hr] using width_eq block)
      (by
        rw [width_eq block, hr]
        exact ⟨Nat.card block.Points, by ring⟩)
      (1 / 18) _
  · unfold preE7CharacterRho
    norm_num
  · exact budget_two_ternary_two block e he

private theorem primePowerRate_two_nine
    (e : ℕ) (he : 9 ≤ e) :
    ActualWreathCompressionTower.traceyPrimePowerRate 2 e 2 ≤
      (63 / 256 : ℝ) * (2 ^ e : ℕ) := by
  unfold ActualWreathCompressionTower.traceyPrimePowerRate
  rw [if_pos rfl]
  simp only [Nat.reduceSubDiff, Nat.mul_one]
  have hmiddle : (256 : ℝ) * (e.choose (e / 2) : ℝ) ≤
      63 * (2 : ℝ) ^ e := by
    exact_mod_cast binary_middle_le_sixtyThree_twoFiftySix e he
  have hp : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  norm_num [Nat.cast_pow] at hmiddle ⊢
  field_simp
  nlinarith

private theorem budget_two_primePower_nine
    (e : ℕ) (he : 9 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimePowerRate 2 e) 2 ≤
      (63 / 512 : ℝ) * (2 ^ e : ℕ) := by
  rw [refinedWeightedFactorBudget_two]
  have h := primePowerRate_two_nine e he
  nlinarith

noncomputable def of_degreeTwo_binaryPrimePowerNine
    (hr : Nat.card block.Fibre = 2)
    (e : ℕ) (he : 9 ≤ e) (hs : blocks block = 2 ^ e) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimePower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P 2 e 2 Nat.prime_two (by omega) hs (by norm_num)
      (component_card_dvd_2 block P hr)
  apply smallAffine_even_budget_margin 2 (blocks block) w
      (by simpa only [hr] using width_eq block)
      (by
        rw [width_eq block, hr]
        exact Even.mul_left (even_iff_two_dvd.mpr
          (by change 2 ∣ blocks block; rw [hs]; exact dvd_pow_self 2 (by omega))) 2)
      (63 / 512) _
  · unfold preE7CharacterRho
    norm_num
  · rw [hs]
    exact budget_two_primePower_nine e he

private theorem sqrt_two_over_three_e_le_oneTwentySeven_fiveTwelve
    (e : ℕ) (he : 11 ≤ e) :
    Real.sqrt (2 / (3 * (e : ℝ))) ≤ (127 : ℝ) / 512 := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · norm_num
  · have hden : (33 : ℝ) ≤ 3 * e := by
      exact_mod_cast (Nat.mul_le_mul_left 3 he)
    have hfrac : (2 : ℝ) / (3 * e) ≤ 2 / 33 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
    norm_num at hfrac ⊢
    nlinarith

private theorem budget_two_binary_eleven
    (e : ℕ) (he : 11 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate (blocks block) 2 e) 2 ≤
      (127 / 1024 : ℝ) * blocks block := by
  rw [refinedWeightedFactorBudget_two]
  have h2 : ActualWreathCompressionTower.traceyPrimaryRate
      (blocks block) 2 e 2 ≤ (blocks block : ℝ) * (127 / 512 : ℝ) := by
    apply traceyPrimaryRate_matching_le
    convert sqrt_two_over_three_e_le_oneTwentySeven_fiveTwelve e he using 1
    all_goals norm_num
  nlinarith

noncomputable def of_degreeTwo_binaryEleven
    (hr : Nat.card block.Fibre = 2)
    (e : ℕ) (he : 11 ≤ e) (hdiv : 2 ^ e ∣ blocks block)
    (hmax : ¬ 2 ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P 2 e 2 Nat.prime_two (by omega) hdiv hmax (by norm_num)
      (component_card_dvd_2 block P hr)
  apply smallAffine_even_budget_margin 2 (blocks block) w
      (by simpa only [hr] using width_eq block)
      (by
        rw [width_eq block, hr]
        exact Even.mul_left (even_iff_two_dvd.mpr
          (dvd_trans (dvd_pow_self 2 (by omega)) hdiv)) 2)
      (127 / 1024) _
  · unfold preE7CharacterRho
    norm_num
  · exact budget_two_binary_eleven block e he

/-- The exact pair-frame exception set. -/
def IsDegreeTwoAffineExceptionalBlockCount (s : ℕ) : Prop :=
  (∃ a : ℕ, 1 ≤ a ∧ a ≤ 8 ∧ s = 2 ^ a) ∨
    (∃ a : ℕ, a ≤ 10 ∧ s = 3 * 2 ^ a)

/-- Degree two: every block count is accepted unless it is one of the
literal pair-frame counts already assigned to a pair sector. -/
noncomputable def degreeTwoExhaustion
    (hr : Nat.card block.Fibre = 2) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P ⊕
      PLift (IsDegreeTwoAffineExceptionalBlockCount (blocks block)) := by
  by_cases hlarge : ∃ q : ℕ, q.Prime ∧ q ∣ blocks block ∧ 5 ≤ q
  · let q := Classical.choose hlarge
    have hqdata := Classical.choose_spec hlarge
    let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      hqdata.1 hqdata.2.1
    exact .inl (of_degreeTwo_largePrime hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm block P hr q E.e hqdata.1 hqdata.2.2
        E.one_le E.pow_dvd E.pow_succ_not_dvd)
  by_cases h9 : 3 ^ 2 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      (by norm_num : Nat.Prime 3) (dvd_trans (by norm_num : 3 ∣ 3 ^ 2) h9)
    have he : 2 ≤ E.e := by
      simpa only [E, ExactPrimaryDivisor.ofPrimeDvd] using
        (valuation_ge_of_pow_dvd block (by norm_num : Nat.Prime 3) h9)
    exact .inl (of_degreeTwo_ternaryTwo hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm block P hr E.e he E.pow_dvd
        E.pow_succ_not_dvd)
  by_cases h3 : 3 ∣ blocks block
  · by_cases h2048 : 2 ^ 11 ∣ blocks block
    · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
        Nat.prime_two (dvd_trans (by norm_num : 2 ∣ 2 ^ 11) h2048)
      have he : 11 ≤ E.e := by
        simpa only [E, ExactPrimaryDivisor.ofPrimeDvd] using
          (valuation_ge_of_pow_dvd block Nat.prime_two h2048)
      exact .inl (of_degreeTwo_binaryEleven hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P hr E.e he E.pow_dvd
          E.pow_succ_not_dvd)
    · have hdvd : blocks block ∣ 2 ^ 10 * 3 ^ 1 :=
        dvd_binary_ternary_bounded (blocks_ne_zero block) hlarge h2048 h9
      let k := Classical.choose h3
      have hk : blocks block = 3 * k := by
        have hk0 := Classical.choose_spec h3
        change blocks block = 3 * k at hk0
        simpa [Nat.mul_comm] using hk0
      have hkdiv : k ∣ 2 ^ 10 := by
        have hmul : 3 * k ∣ 3 * 2 ^ 10 := by
          rw [hk] at hdvd
          simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hdvd
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) hmul
      let a := Classical.choose ((Nat.dvd_prime_pow Nat.prime_two).mp hkdiv)
      have haspec := Classical.choose_spec
        ((Nat.dvd_prime_pow Nat.prime_two).mp hkdiv)
      have ha : a ≤ 10 := haspec.1
      have hka : k = 2 ^ a := haspec.2
      exact .inr ⟨Or.inr ⟨a, ha, by rw [hk, hka]⟩⟩
  · by_cases h512 : 2 ^ 9 ∣ blocks block
    · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
        Nat.prime_two (dvd_trans (by norm_num : 2 ∣ 2 ^ 9) h512)
      have he : 9 ≤ E.e := by
        simpa only [E, ExactPrimaryDivisor.ofPrimeDvd] using
          (valuation_ge_of_pow_dvd block Nat.prime_two h512)
      have hdvd : blocks block ∣ 2 ^ E.e := by
        simpa only [pow_zero, mul_one] using
          (dvd_binary_ternary_bounded (a := E.e) (b := 0)
          (blocks_ne_zero block) hlarge
          E.pow_succ_not_dvd (by
            simpa only [Nat.zero_add, pow_one] using h3))
      have hs : blocks block = 2 ^ E.e :=
        Nat.dvd_antisymm hdvd E.pow_dvd
      exact .inl (of_degreeTwo_binaryPrimePowerNine hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P hr E.e he hs)
    · have hdvd : blocks block ∣ 2 ^ 8 := by
        simpa using dvd_binary_ternary_bounded (a := 8) (b := 0)
          (blocks_ne_zero block) hlarge h512
            (by simpa only [Nat.zero_add, pow_one] using h3)
      let a := Classical.choose ((Nat.dvd_prime_pow Nat.prime_two).mp hdvd)
      have haspec := Classical.choose_spec
        ((Nat.dvd_prime_pow Nat.prime_two).mp hdvd)
      have ha : a ≤ 8 := haspec.1
      have hsa : blocks block = 2 ^ a := haspec.2
      have ha1 : 1 ≤ a := by
        by_contra ha0
        have : a = 0 := by omega
        have hs1 : blocks block = 1 := by simpa [this] using hsa
        have hs2 := block.degrees_ge_two.2
        change 2 ≤ blocks block at hs2
        omega
      exact .inr ⟨Or.inl ⟨a, ha1, ha, hsa⟩⟩

end ComponentSource
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
