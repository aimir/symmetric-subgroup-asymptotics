import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreNumerics
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveDegreeFourS4Exhaustion

/-!
# Exhausting the degree-four zero-core capacity exceptions

Once the ternary core vanishes, the literal block top is faithful and the
only numerical demand is the binary rank-two induced capacity.  An odd
prime divisor of the block count gives capacity at most `2s/3`; a binary
count `2^e` gives the same bound from `e = 5` onward.  On the finite
exception menu this leaves exactly `2, 4, 8, 16` blocks.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

private abbrev blocks := Nat.card block.Points

/-- An odd prime divisor of the actual block count supplies the required
`2s/3` capacity on the zero-core branch. -/
noncomputable def degreeFourZeroCoreSource_of_oddPrime
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hdiv : q ∣ blocks block) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  apply degreeFourZeroCoreSource_of_capacity block P hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm hr hD
  intro H href
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    omega
  have h := href.primeTo q 1 hq hq2 (by norm_num) (by simpa using hdiv)
  calc
    H ≤ (2 : ℝ) * blocks block / q := by simpa using h
    _ ≤ (2 : ℝ) * blocks block / 3 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num)
        (by exact_mod_cast hq3)

/-- A binary block count `2^e` supplies the required capacity from exponent
five onward. -/
noncomputable def degreeFourZeroCoreSource_of_binaryPower
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (e : ℕ) (he : 5 ≤ e) (hs : blocks block = 2 ^ e) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  apply degreeFourZeroCoreSource_of_capacity block P hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm hr hD
  intro H href
  have he1 : 1 ≤ e := by omega
  have h := href.primePower 2 e Nat.prime_two he1 hs
  have hmiddleNat := binary_middle_le_five_sixteenths e he
  have hmiddle : (e.choose (e / 2) : ℝ) / (2 : ℝ) ^ e ≤ 5 / 16 := by
    have hcast : (16 : ℝ) * e.choose (e / 2) ≤ 5 * (2 : ℝ) ^ e := by
      exact_mod_cast hmiddleNat
    have hpow : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
    apply (div_le_iff₀ hpow).2
    nlinarith
  calc
    H ≤ (2 : ℝ) * blocks block * e.choose (e / 2) / (2 : ℝ) ^ e := by
      simpa only [Nat.reduceSubDiff, Nat.mul_one] using h
    _ = ((2 : ℝ) * blocks block) *
        ((e.choose (e / 2) : ℝ) / (2 : ℝ) ^ e) := by ring
    _ ≤ ((2 : ℝ) * blocks block) * (5 / 16 : ℝ) :=
      mul_le_mul_of_nonneg_left hmiddle (by positivity)
    _ ≤ (2 : ℝ) * blocks block / 3 := by
      have hs0 : (0 : ℝ) ≤ blocks block := by positivity
      nlinarith

/-- The exact finite residue of the zero-core capacity argument. -/
def IsDegreeFourZeroCoreResidualBlockCount (s : ℕ) : Prop :=
  s = 2 ∨ s = 4 ∨ s = 8 ∨ s = 16

/-- Exhaust the old degree-four capacity menu on the zero-core branch,
leaving only the four finite power-of-two frames. -/
noncomputable def degreeFourZeroCoreExceptionalExhaustion
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (hs : ComponentSource.IsDegreeFourTwentyFourExceptionalBlockCount
      (blocks block)) :
    PreE7RankTailSourceOrYonedaTopData w U ⊕
      PLift (IsDegreeFourZeroCoreResidualBlockCount (blocks block)) := by
  by_cases hbinary : ∃ a : ℕ, 1 ≤ a ∧ a ≤ 8 ∧ blocks block = 2 ^ a
  · let a := Classical.choose hbinary
    have ha := Classical.choose_spec hbinary
    change 1 ≤ a ∧ a ≤ 8 ∧ blocks block = 2 ^ a at ha
    by_cases ha5 : 5 ≤ a
    · exact .inl (degreeFourZeroCoreSource_of_binaryPower block P
        hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hD
        a ha5 ha.2.2)
    · have ha4 : a ≤ 4 := by omega
      have hsres : IsDegreeFourZeroCoreResidualBlockCount (blocks block) := by
        rw [ha.2.2]
        have ha1 : 1 ≤ a := ha.1
        interval_cases a <;>
          norm_num [IsDegreeFourZeroCoreResidualBlockCount]
      exact .inr ⟨hsres⟩
  by_cases hthree : ∃ a : ℕ, a ≤ 10 ∧ blocks block = 3 * 2 ^ a
  · let a := Classical.choose hthree
    have ha := Classical.choose_spec hthree
    exact .inl (degreeFourZeroCoreSource_of_oddPrime block P
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hD
      3 (by norm_num) (by norm_num) (by
        rw [ha.2]
        exact dvd_mul_right 3 (2 ^ a)))
  by_cases h5 : blocks block = 5
  · exact .inl (degreeFourZeroCoreSource_of_oddPrime block P
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hD
      5 (by norm_num) (by norm_num) (by rw [h5]))
  by_cases h10 : blocks block = 10
  · exact .inl (degreeFourZeroCoreSource_of_oddPrime block P
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hD
      5 (by norm_num) (by norm_num) (by rw [h10]; norm_num))
  by_cases h15 : blocks block = 15
  · exact .inl (degreeFourZeroCoreSource_of_oddPrime block P
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hD
      3 (by norm_num) (by norm_num) (by rw [h15]; norm_num))
  by_cases h20 : blocks block = 20
  · exact .inl (degreeFourZeroCoreSource_of_oddPrime block P
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hD
      5 (by norm_num) (by norm_num) (by rw [h20]; norm_num))
  by_cases h30 : blocks block = 30
  · exact .inl (degreeFourZeroCoreSource_of_oddPrime block P
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hD
      3 (by norm_num) (by norm_num) (by rw [h30]; norm_num))
  by_cases h60 : blocks block = 60
  · exact .inl (degreeFourZeroCoreSource_of_oddPrime block P
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hD
      3 (by norm_num) (by norm_num) (by rw [h60]; norm_num))
  · exfalso
    rcases hs with hpair | h5' | h10' | h15' | h20' | h30' | h60'
    · exact hpair.elim hbinary hthree
    · exact h5 h5'
    · exact h10 h10'
    · exact h15 h15'
    · exact h20 h20'
    · exact h30 h30'
    · exact h60 h60'

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
