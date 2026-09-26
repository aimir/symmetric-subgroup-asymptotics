import SymmetricSubgroupAsymptotics.BinaryCarrierWordWeightMass

/-! Unit weights count the literal original normal histories. They do not
include action normalizers, orbit-profile factorials or owner weights.
The complete normal multiplicity is bounded from the actual factor orders.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierWord

attribute [local instance] Fintype.ofFinite

/-- One for every normal axis at every original word position. -/
def unitAxisWeights : (w : List Factor) → AxisWeights w
  | [] => PUnit.unit
  | _ :: w => (fun _ => 1, unitAxisWeights w)

theorem unitAxisWeights_nonnegative (w : List Factor) :
    WeightsNonnegative w (unitAxisWeights w) := by
  induction w with
  | nil => exact True.intro
  | cons A w ih => exact ⟨fun _ => zero_le_one, ih⟩

theorem unitAxisWeights_le_one (w : List Factor) :
    WeightsLe w (unitAxisWeights w) 1 := by
  induction w with
  | nil => exact True.intro
  | cons A w ih => exact ⟨fun _ => le_rfl, ih⟩

/-- Every complete original full subgroup receives weight one, including
the unique full subgroup of the empty product. -/
@[simp] theorem weight_unitAxisWeights (w : List Factor) :
    ∀ H : Family w, weight w (unitAxisWeights w) H = 1 := by
  induction w with
  | nil => intro H; rfl
  | cons A w ih =>
      intro H
      change 1 * weight w (unitAxisWeights w) (tail A w H) = 1
      rw [ih, one_mul]

@[simp] theorem historyWeight_unitAxisWeights (w : List Factor) :
    ∀ h : History w, historyWeight w (unitAxisWeights w) h = 1 := by
  induction w with
  | nil => intro h; rfl
  | cons A w ih =>
      intro h
      change 1 * historyWeight w (unitAxisWeights w) h.2 = 1
      rw [ih, one_mul]

/-- The axis product counts all actual normal histories, not numerical
envelope labels or isomorphism classes. -/
theorem axisWeightProduct_unitAxisWeights (w : List Factor) :
    axisWeightProduct w (unitAxisWeights w) = (Nat.card (History w) : ℝ) := by
  rw [← historyWeight_sum_eq_axisWeightProduct]
  simp only [historyWeight_unitAxisWeights, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_eq_nat_card]

/-- No per-normal weight bound remains as an input: the unit bound is
proved, and the actual order cap supplies the entire normal multiplicity. -/
theorem axisWeightProduct_unitAxisWeights_le_of_orderBound
    (w : List Factor) (b : ℕ) (hb : OrderBound w b) :
    axisWeightProduct w (unitAxisWeights w) ≤
      (2 : ℝ)^((2^b : ℕ)*w.length) := by
  have h := axisWeightProduct_le_of_orderBound w b hb (unitAxisWeights w)
    (unitAxisWeights_nonnegative w) 1 zero_le_one (unitAxisWeights_le_one w)
  simpa only [one_mul, pow_mul] using h

theorem history_card_le_of_orderBound
    (w : List Factor) (b : ℕ) (hb : OrderBound w b) :
    (Nat.card (History w) : ℝ) ≤ (2 : ℝ)^((2^b : ℕ)*w.length) := by
  rw [← axisWeightProduct_unitAxisWeights]
  exact axisWeightProduct_unitAxisWeights_le_of_orderBound w b hb

end SymmetricSubgroupAsymptotics.BinaryCarrierWord
