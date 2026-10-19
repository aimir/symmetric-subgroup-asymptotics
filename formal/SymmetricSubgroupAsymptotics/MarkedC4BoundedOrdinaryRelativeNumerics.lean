import SymmetricSubgroupAsymptotics.MarkedC4BoundedOrdinaryRelativeRow
import SymmetricSubgroupAsymptotics.MarkedC4PublishedEncodingReduction

/-! The actual fixed-cutoff tuples have length O_C(√b), and their full
symmetric-alphabet cost is O_C(b^(3/2) log b). These numerical proofs finish
the constructed relative-generator reduction from ordinary published
Theorem 7, Lemma 8.5, and Kovács--Praeger. No marked counting input occurs. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.BoundedOrdinaryRelativeRow

def lengthConstant (C : ℕ) : ℝ := 8*(C.factorial : ℝ)+1

theorem lengthConstant_pos (C : ℕ) : 0 < lengthConstant C := by
  unfold lengthConstant
  positivity

theorem tupleLength_le_sqrt (C : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    (tupleLength C b : ℝ) ≤ lengthConstant C * Real.sqrt b := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hs : 1 ≤ Real.sqrt (b : ℝ) := by
    exact (Real.le_sqrt (by norm_num) hb0).mpr (by nlinarith)
  have hs2 : Real.sqrt ((2*b : ℕ) : ℝ) ≤ 2*Real.sqrt b := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · push_cast
      nlinarith [Real.sq_sqrt hb0]
  have hl : (tupleLength C b : ℝ) ≤
      4*(C.factorial : ℝ)*Real.sqrt ((2*b : ℕ) : ℝ)+1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hm := mul_le_mul_of_nonneg_left hs2
    (show 0 ≤ 4*(C.factorial : ℝ) by positivity)
  unfold lengthConstant
  nlinarith

theorem eventually_sqrt_le_linear {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ b : ℕ in atTop, Real.sqrt (b : ℝ) ≤ δ*b := by
  filter_upwards [eventually_ge_atTop (⌈1/δ^2⌉₊)] with b hb
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hlarge : 1/δ^2 ≤ (b : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hb)
  have hsq : 0 < δ^2 := sq_pos_of_pos hδ
  have hmul : 1 ≤ δ^2*(b : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hsq).mp hlarge
  have hm := mul_le_mul_of_nonneg_right hmul hb0
  apply Real.sqrt_le_iff.mpr
  exact ⟨by positivity,by nlinarith⟩

theorem tupleLength_sublinear (C : ℕ) : OneVariableSublinear (tupleLength C) := by
  intro ε hε
  have hA := lengthConstant_pos C
  filter_upwards [eventually_ge_atTop 1,
    eventually_sqrt_le_linear (div_pos hε hA)] with b hb hs
  calc
    (tupleLength C b : ℝ) ≤ lengthConstant C*Real.sqrt b := tupleLength_le_sqrt C hb
    _ ≤ lengthConstant C*((ε/lengthConstant C)*b) :=
      mul_le_mul_of_nonneg_left hs hA.le
    _ = ε*b := by field_simp

theorem alphabet_log_le (b : ℕ) :
    Real.logb 2 (Fintype.card (⊤ : Subgroup (PermutationGroup b)) : ℝ) ≤
      (b : ℝ)*Real.log ((b : ℝ)+2)/Real.log 2 := by
  have hc : Fintype.card (⊤ : Subgroup (PermutationGroup b)) = b.factorial := by
    simp [PermutationGroup,Fintype.card_perm]
  have hfac : b.factorial ≤ (b+2)^b :=
    b.factorial_le_pow.trans (Nat.pow_le_pow_left (by omega) _)
  have hlog := Real.log_le_log (show 0 < (b.factorial : ℝ) by positivity)
    (show (b.factorial : ℝ) ≤ ((b : ℝ)+2)^b by exact_mod_cast hfac)
  rw [Real.log_pow] at hlog
  rw [hc,Real.logb]
  exact div_le_div_of_nonneg_right hlog (Real.log_pos (by norm_num)).le

theorem tupleCost_nonneg (C b : ℕ) : 0 ≤ tupleCost C b := by
  unfold tupleCost
  apply mul_nonneg _ (by positivity)
  apply Real.logb_nonneg (by norm_num : (1 : ℝ)<2)
  exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty
    (⊤ : Subgroup (PermutationGroup b))))

theorem tupleCost_subquadratic (C : ℕ) : OneVariableSubquadratic (tupleCost C) := by
  refine ⟨tupleCost_nonneg C,?_⟩
  intro ε hε
  have hA := lengthConstant_pos C
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_ge_atTop 1,
    BinaryMixtureNumerics.eventually_log_error_le_sqrt
      (lengthConstant C/Real.log 2) (by positivity) hε] with b hb hlog
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hs0 := Real.sqrt_nonneg (b : ℝ)
  have hx : 0 ≤ (b : ℝ)*Real.log ((b : ℝ)+2)/Real.log 2 := by
    have : 0 ≤ Real.log ((b : ℝ)+2) := Real.log_nonneg (by linarith)
    positivity
  calc
    tupleCost C b ≤ ((b : ℝ)*Real.log ((b : ℝ)+2)/Real.log 2)*tupleLength C b :=
      mul_le_mul_of_nonneg_right (alphabet_log_le b) (by positivity)
    _ ≤ ((b : ℝ)*Real.log ((b : ℝ)+2)/Real.log 2)*
        (lengthConstant C*Real.sqrt b) :=
      mul_le_mul_of_nonneg_left (tupleLength_le_sqrt C hb) hx
    _ = ((b : ℝ)*Real.sqrt b)*
        ((lengthConstant C/Real.log 2)*Real.log ((b : ℝ)+2)) := by ring
    _ ≤ ((b : ℝ)*Real.sqrt b)*(ε*Real.sqrt b) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = ε*(b : ℝ)^2 := by
      calc
        _ = ε*(b : ℝ)*(Real.sqrt (b : ℝ))^2 := by ring
        _ = _ := by rw [Real.sq_sqrt hb0]; ring

/-- Every structural field and both numerical fields are constructed.
The historical name of the target structure does not add an assumption. -/
def reduction
    (hsub : OrdinaryNilpotentGeneration.PublishedSolubleSubdirectHeight)
    (hseven : OrdinaryNilpotentGeneration.PublishedTheoremSeven)
    (hKP : KovacsPraegerAbelianizationBound) (C : ℕ) :
    PublishedRelativeGeneratorReduction
      (OrbitCutoffFamilies.solubleCount C) (OrbitCutoffFamilies.nilpotentCount C) where
  q := tupleCost C
  l := tupleLength C
  q_subquadratic := tupleCost_subquadratic C
  l_sublinear := tupleLength_sublinear C
  row := relativeRow hsub hseven hKP C

end SymmetricSubgroupAsymptotics.MarkedC4.BoundedOrdinaryRelativeRow
end
