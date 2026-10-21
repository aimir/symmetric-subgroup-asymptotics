import SymmetricSubgroupAsymptotics.MarkedC4ActualBoundedBinaryError
import SymmetricSubgroupAsymptotics.PermutationAbelianQuotientOrderBound
import SymmetricSubgroupAsymptotics.BinaryExcessProposition53Proof
import SymmetricSubgroupAsymptotics.BinaryOriginalWordConsequences
import SymmetricSubgroupAsymptotics.BinaryNormalFTheorem57Proof
import SymmetricSubgroupAsymptotics.BinaryDerivedNormalQuarterProof
import SymmetricSubgroupAsymptotics.RDTDegreeEightExceptionalProof
import SymmetricSubgroupAsymptotics.RDTBoundedFactorEpimorphismProof

/-! A genuinely independent sharp counting leaf. The ordinary bounded
binary family is obtained by setting the mark rank to zero in the proved
actual-word theorem. All its former literature hypotheses are installed
by proved theorems. In particular neither hodd nor T1 occurs as a premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrdinaryBoundedBinaryCount
open MarkedC4

private def epiInput : RDTNormalFInterface.RDTTheorem46BinaryInput :=
  RDTBoundedFactorEpimorphismProof.rdtTheorem46BinaryInput_proved

def coefficient (C : ℕ) : ℝ :=
  SkeletonMenuError.coefficient C+HistoryMenuError.coefficient epiInput C+8

theorem coefficient_nonneg (C : ℕ) : 0≤coefficient C := by
  have hs := SkeletonMenuError.coefficient_nonneg C
  have hh := HistoryMenuError.coefficient_nonneg epiInput C
  unfold coefficient
  linarith

/-- Every literal original bounded-orbit binary subgroup is counted;
there is no conjugacy quotient, abstract model replacement or count input. -/
theorem bounded_binary_card_le (C b : ℕ) (hb : 1≤b) :
    (Nat.card (BoundedNilpotentTargetConvolution.BinaryFamily C b) : ℝ) ≤
      (2 : ℝ)^((b : ℝ)^2/16+coefficient C*b*Real.logb 2 ((b : ℝ)+2)) := by
  have hcount := ActualBoundedBinaryError.marked_bound
    PermutationAbelianQuotientOrderBound.kovacsPraegerBinaryAbelianQuotientBound
    (publishedTheorem55Binary_of_proposition53 publishedProposition53Binary_proved)
    publishedProposition53Binary_proved publishedTheorem57Binary_proved
    RDTDegreeEightExceptionalProof.publishedDegreeEightExceptional
    publishedDerivedNormalQuarterBinary_proved epiInput C b 0
  have herr : ActualBoundedBinaryError.error epiInput C b 0 ≤
      coefficient C*b*Real.logb 2 ((b : ℝ)+2) := by
    have hs := SingleMarkError.error_le_boundedWordError hb 0
    unfold ActualBoundedBinaryError.error
    apply (add_le_add (add_le_add hs le_rfl) le_rfl).trans_eq
    unfold boundedWordError coefficient Real.logb
    push_cast
    ring
  have hc : (Nat.card (BoundedNilpotentTargetConvolution.BinaryFamily C b) : ℝ) ≤
      (2 : ℝ)^((b : ℝ)^2/16+ActualBoundedBinaryError.error epiInput C b 0) := by
    simpa only [BoundedNilpotentTargetConvolution.binaryMoment,pow_zero,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
      Nat.card_eq_fintype_card,Nat.cast_zero,mul_zero,zero_pow (by decide : 2≠0),
      zero_div,add_zero,markedF] using hcount
  exact hc.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (add_le_add le_rfl herr))

/-- The sharp bounded binary estimate has one absolute coefficient at
each fixed cutoff, without any retained published assumption. -/
theorem exists_bounded_binary_coefficient (C : ℕ) :
    ∃ A : ℝ,0≤A ∧ ∀ b : ℕ,1≤b →
      (Nat.card (BoundedNilpotentTargetConvolution.BinaryFamily C b) : ℝ) ≤
        (2 : ℝ)^((b : ℝ)^2/16+A*b*Real.logb 2 ((b : ℝ)+2)) :=
  ⟨coefficient C,coefficient_nonneg C,bounded_binary_card_le C⟩

end SymmetricSubgroupAsymptotics.CFSGOrdinaryBoundedBinaryCount
