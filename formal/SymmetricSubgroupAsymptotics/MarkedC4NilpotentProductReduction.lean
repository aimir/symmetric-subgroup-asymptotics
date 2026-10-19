import SymmetricSubgroupAsymptotics.MarkedC4NilpotentTargetConvolution
import SymmetricSubgroupAsymptotics.MarkedC4PublishedEncodingReduction

/-! The concrete original nilpotent physical encoding instantiates the
existing PublishedProductReduction structure. The historical name of that
structure supplies no premise: all its encoding fields are constructed. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.NilpotentProductReduction
open NilpotentPhysicalProductEncoding

def sourceCount (b r : ℕ) : ℝ :=
  ∑ K : Source b, (Nat.card (K.1 →* Multiplicative (ZMod 4)) : ℝ)^r
def targetCount (b r : ℕ) : ℝ :=
  ∑ z : Target b, (Nat.card (z.1.2.2.1 →* Multiplicative (ZMod 4)) : ℝ)^r

def labelCost (b : ℕ) : ℝ := (3 : ℝ)*b*Real.log ((b : ℝ)+1)/Real.log 2

theorem labelCost_nonneg (b : ℕ) : 0≤labelCost b := by
  unfold labelCost
  have hlog : 0≤Real.log ((b : ℝ)+1) := Real.log_nonneg (by
    have hb := Nat.cast_nonneg (α := ℝ) b
    linarith)
  positivity

theorem labelCost_le_error (b : ℕ) : labelCost b≤boundedWordError 2 b 0 := by
  have hlog : Real.log ((b : ℝ)+1)≤Real.log ((b : ℝ)+2) :=
    Real.log_le_log (by positivity) (by linarith)
  unfold labelCost boundedWordError
  push_cast
  simp only [add_zero]
  have hd : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hlog (show 0≤(3 : ℝ)*b by positivity)
  apply (div_le_iff₀ hd).mpr
  field_simp
  nlinarith

theorem labelCost_subquadratic : OneVariableSubquadratic labelCost := by
  refine ⟨labelCost_nonneg,?_⟩
  intro ε hε
  filter_upwards [boundedWordError_negligible (A := 2) (by norm_num) ε hε 0] with b hb
  have h := (labelCost_le_error b).trans (hb 0 (by simp))
  simpa only [Nat.cast_zero,add_zero] using h

/-- Exact finite cardinality, with a genuinely subquadratic logarithm. -/
theorem alphabet_bound (b : ℕ) :
    (Fintype.card (PhysicalGridLabels.Code b) : ℝ)≤(2 : ℝ)^(labelCost b) := by
  rw [PhysicalGridLabels.card_code]
  have he : labelCost b=Real.logb 2 ((b : ℝ)+1)*((3*b : ℕ) : ℝ) := by
    unfold labelCost Real.logb
    push_cast
    ring
  rw [he,Real.rpow_mul (by norm_num : (0 : ℝ)≤2),
    Real.rpow_logb (by norm_num : (0 : ℝ)<2) (by norm_num : (2 : ℝ)≠1) (by positivity),
    Real.rpow_natCast]
  push_cast
  rfl

def row (b : ℕ) : ProductEncodingRow sourceCount targetCount labelCost b where
  A := Source b
  B := Target b
  C := PhysicalGridLabels.Code b
  fintypeA := inferInstance
  fintypeB := inferInstance
  fintypeC := inferInstance
  source K := K.1
  target z := z.1.2.2.1
  sourceGroup _ := inferInstance
  sourceFinite _ := inferInstance
  targetGroup _ := inferInstance
  targetFinite _ := inferInstance
  encoding := NilpotentPhysicalProductEncoding.encoding b
  source_identity _ := rfl
  target_identity _ := rfl
  auxiliary_bound := alphabet_bound b

/-- A constructed structural product reduction, not a new published axiom. -/
def reduction : PublishedProductReduction sourceCount targetCount where
  q := labelCost
  q_subquadratic := labelCost_subquadratic
  row := row

/-- The target count is controlled by the exact physical convolution. -/
theorem target_le_convolution (b r : ℕ) : targetCount b r≤
    PhysicalOddConvolution.count NilpotentTargetConvolution.binaryMoment
      NilpotentTargetConvolution.oddCount b r :=
  NilpotentTargetConvolution.target_sum_le b r
end SymmetricSubgroupAsymptotics.MarkedC4.NilpotentProductReduction
