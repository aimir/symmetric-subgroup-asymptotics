import SymmetricSubgroupAsymptotics.OriginalBinaryAffineSmallSharedSteps

/-! Actual binary affine defining-primary induction, now with only four
explicit pairs left unpaid. Three of the numerical seven-pair failures
are removed by proved group structure. No stronger smaller-MN premise
is inserted: the sole generator hypothesis is the SAME actual smaller
top ceiling. In particular d=2,e=2 remains an explicit residual. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineFourResidualSteps
open OriginalAffineBlockCharacteristicHead

def unpaidFour (d e : ℕ) : Bool :=
  (d == 2 && e == 2) || (d == 4 && (e == 1 || e == 2)) || (d == 5 && e == 1)

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

/-- The residual guard is exactly (2,2),(4,1),(4,2),(5,1). Nothing is
claimed for these four pairs or for non-power-of-two top degrees. -/
theorem genRank_le_ceiling_outside_four (hp : P.p = 2) (e : ℕ) (he : 1 ≤ e)
    (ht : Fintype.card block.Points = 2^e) (i : block.Points)
    (hpaid : unpaidFour (translationDimension J block P) e = false)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let d := translationDimension J block P
  by_cases hold : BinaryAffineJointBoundedWindows.unpaid d e = false
  · exact OriginalBinaryAffineJointWindowStep.genRank_le_ceiling_outside_unpaid
      J block P hp e he ht i hold htop
  · have hbad : BinaryAffineJointBoundedWindows.unpaid d e = true := by
      cases hx : BinaryAffineJointBoundedWindows.unpaid d e
      · exact False.elim (hold hx)
      · rfl
    have hcases : (d = 2 ∧ e = 1) ∨ (d = 3 ∧ (e = 1 ∨ e = 2)) := by
      have hb : ((d = 2 ∨ d = 3 ∨ d = 4) ∧ (e = 1 ∨ e = 2)) ∨
          (d = 5 ∧ e = 1) := by
        simpa [BinaryAffineJointBoundedWindows.unpaid, or_assoc] using hbad
      have hp' : ¬((d = 2 ∧ e = 2) ∨ (d = 4 ∧ (e = 1 ∨ e = 2)) ∨
          (d = 5 ∧ e = 1)) := by
        simpa [unpaidFour, d, and_assoc, or_assoc] using hpaid
      omega
    rcases hcases with ⟨hd, heq⟩ | ⟨hd, hesmall⟩
    · have ht2 : Fintype.card block.Points = 2 := by simpa only [heq, pow_one] using ht
      exact OriginalBinaryAffineSmallSharedSteps.two_dim_two_blocks J block P hp hd ht2 i
    · have hf := fibre_card_eq_prime_pow_dimension J block P
      change Nat.card block.Fibre = P.p^d at hf
      rw [hp, hd] at hf
      have hdegree : Nat.card block.Fibre = 8 := hf
      exact OriginalBinaryAffineSmallSharedSteps.degreeEight_two_or_four_blocks
        J block P hdegree e hesmall ht htop

theorem exists_generating_finset (hp : P.p = 2) (e : ℕ) (he : 1 ≤ e)
    (ht : Fintype.card block.Points = 2^e) (i : block.Points)
    (hpaid : unpaidFour (translationDimension J block P) e = false)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧
      S.card ≤ traceyPermutationGeneratorCeiling n := by
  obtain ⟨S, hcard, hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨S, hgen, hcard.le.trans
    (genRank_le_ceiling_outside_four J block P hp e he ht i hpaid htop)⟩

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineFourResidualSteps
