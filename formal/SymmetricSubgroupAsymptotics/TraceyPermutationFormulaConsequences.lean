import SymmetricSubgroupAsymptotics.PermutationStabilizerInduced
import SymmetricSubgroupAsymptotics.TraceyRefinedAffineInput
import SymmetricSubgroupAsymptotics.TraceyBinaryFormulaInput
import Mathlib.Algebra.Order.Ring.Finset

/-! The binary permutation formula is a specialization of the stronger
retained refined induced-module input. The induction subgroup is the actual
point stabilizer and the local representation is the trivial line. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- The prime-to and prime-power fields of the refined input contain the
two alternatives of the binary formula. -/
theorem traceyRefinedCapacity_binaryFormula {s H d : ℕ} (hs : 2 ≤ s)
    (hb : TraceyRefinedInducedCapacityBounds 2 1 s (H : ℝ))
    (hd : d ≤ H) (hdcard : d ≤ s) : TraceyBinaryFormulaBounds s d := by
  have hs0 : s ≠ 0 := by omega
  by_cases ho1 : ordCompl[2] s = 1
  · left
    let a := s.factorization 2
    have hseq : s = 2 ^ a := by
      simpa only [ho1, mul_one] using
        (Nat.ordProj_mul_ordCompl_eq_self s 2).symm
    have ha : 1 ≤ a := by
      by_contra hn
      have ha0 : a = 0 := by omega
      rw [hseq, ha0] at hs
      norm_num at hs
    have hK : traceyBinaryK s = a := by
      rw [hseq, traceyBinaryK_two_pow]
    refine ⟨?_, ?_⟩
    · simpa only [hseq, Nat.ordProj_self_pow Nat.prime_two] using hdcard
    · have hbound := hb.primePower 2 a Nat.prime_two ha hseq
      dsimp only at hbound
      have hreal : (H : ℝ) * (2 : ℝ) ^ a ≤
          (s : ℝ) * (a.choose (a / 2) : ℝ) := by
        simpa only [Nat.reduceSub, Nat.mul_one, Nat.cast_one, one_mul] using
          (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (a * (2 - 1)))).mp hbound
      have hH : H * 2 ^ a ≤ s * a.choose (a / 2) := by
        exact_mod_cast hreal
      rw [hK]
      exact (Nat.mul_le_mul_left (2 ^ a) hd).trans (by
        simpa only [Nat.mul_comm] using hH)
  · right
    refine ⟨ho1, ?_⟩
    rw [largestPrimePower, max_mul, one_mul, Finset.sup_mul₀]
    apply max_le hdcard
    apply Finset.sup_le
    intro q hq
    have he0 : (ordCompl[2] s).factorization q ≠ 0 :=
      Finsupp.mem_support_iff.mp hq
    have hprime : q.Prime := Nat.prime_of_mem_primeFactors
      (show q ∈ (ordCompl[2] s).primeFactors from hq)
    have hq2 : q ≠ 2 := by
      intro he
      subst q
      exact Nat.not_dvd_ordCompl Nat.prime_two hs0
        (Nat.dvd_of_factorization_pos he0)
    have ho0 : ordCompl[2] s ≠ 0 := (Nat.ordCompl_pos 2 hs0).ne'
    have hdiv : q ^ (ordCompl[2] s).factorization q ∣ s :=
      ((hprime.pow_dvd_iff_le_factorization ho0).mpr le_rfl).trans
        (Nat.ordCompl_dvd s 2)
    have hbound := hb.primeTo q ((ordCompl[2] s).factorization q)
      hprime hq2 (by omega) hdiv
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hprime.pos
    have hreal : (H : ℝ) * (q : ℝ) ^ (ordCompl[2] s).factorization q ≤ s := by
      simpa only [Nat.cast_one, one_mul] using
        (le_div_iff₀ (by positivity :
          (0 : ℝ) < (q : ℝ) ^ (ordCompl[2] s).factorization q)).mp hbound
    have hH : H * q ^ (ordCompl[2] s).factorization q ≤ s := by
      exact_mod_cast hreal
    exact (Nat.mul_le_mul_left _ hd).trans (by
      simpa only [Nat.mul_comm] using hH)

/-- Refined generation of the actual stabilizer's trivial line controls
all subrepresentations of the original permutation module. -/
theorem TraceyRefinedInducedModuleInput.permutation
    (hTracey : TraceyRefinedInducedModuleInput)
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [MulAction.IsPretransitive G X]
    (x : X) (hs : 2 ≤ Nat.card X) :
    ∃ H : ℕ,
      TraceyRefinedInducedCapacityBounds 2 1 (Nat.card X) (H : ℝ) ∧
      UniformSubrepresentationGeneratorBound
        (permutationFunctionRepresentation (ZMod 2) G X) H := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hindex : (MulAction.stabilizer G x).index = Nat.card X :=
    MulAction.index_stabilizer_of_transitive G x
  obtain ⟨H, hb, hgen⟩ := hTracey 2 G (MulAction.stabilizer G x)
    (by simpa only [hindex] using hs) (ZMod 2)
    (Representation.trivial (ZMod 2) (MulAction.stabilizer G x) (ZMod 2))
  refine ⟨H, ?_, ?_⟩
  · simpa only [Module.finrank_self, hindex] using hb
  · exact hgen.of_injective (PermutationStabilizerInduced.toInduced x)
      (PermutationStabilizerInduced.toInduced_injective x)

/-- The formula-level binary input is redundant in the presence of the
retained refined induced-module theorem. -/
theorem TraceyRefinedInducedModuleInput.binaryFormula
    (hTracey : TraceyRefinedInducedModuleInput) : TraceyBinaryFormulaInput := by
  intro G _ _ X _ _ _ M
  let d := Module.finrank (ZMod 2) (M.toRepresentation.IntertwiningMap
    (Representation.trivial (ZMod 2) G (ZMod 2)))
  have hdcard : d ≤ Nat.card X := by
    obtain ⟨v, hv⟩ := PermutationStabilizerInduced.uniform_card
      (k := ZMod 2) (G := G) (X := X) M
    exact representationHead_finrank_le_generators M.toRepresentation v hv
  by_cases hs : 2 ≤ Nat.card X
  · have hnonempty : Nonempty X := (Nat.card_pos_iff.mp (by omega)).1
    obtain ⟨x⟩ := hnonempty
    obtain ⟨H, hb, hgen⟩ := hTracey.permutation G X x hs
    obtain ⟨v, hv⟩ := hgen M
    exact traceyRefinedCapacity_binaryFormula hs hb
      (representationHead_finrank_le_generators M.toRepresentation v hv) hdcard
  · have hsmall : Nat.card X = 0 ∨ Nat.card X = 1 := by omega
    rcases hsmall with hzero | hone
    · have hd0 : d = 0 := by omega
      change TraceyBinaryFormulaBounds (Nat.card X) d
      rw [hzero, hd0]
      left
      simp [traceyBinaryK]
    · change TraceyBinaryFormulaBounds (Nat.card X) d
      rw [hone]
      left
      have hd1 : d ≤ 1 := by omega
      simpa [traceyBinaryK] using And.intro hd1 hd1

end SymmetricSubgroupAsymptotics
