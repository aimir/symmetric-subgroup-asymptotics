import SymmetricSubgroupAsymptotics.MarkedC4SolubleContainerOrder
import SymmetricSubgroupAsymptotics.Non2PreE7MenuMassAggregation
import SymmetricSubgroupAsymptotics.MarkedC4ErrorCalculus
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! The retained labelled transitive-group count gives the weaker
subquadratic count needed for the literal soluble-container menu. No
conjugacy-class estimate for maximal soluble groups is asserted. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.MarkedC4.LMMSubquadraticSolubleContainers
open LiteralSolubleOrbitContainers SolubleContainerCount

private def localToLabelled (X : Type) [Fintype X] :
    LocalContainer X → LabelledTransitiveSubgroup (Fintype.card X) := by
  let e := Fintype.equivFin X
  intro D
  refine ⟨D.val.map e.permCongrHom.toMonoidHom, ⟨?_⟩⟩
  intro x y
  obtain ⟨g, hg⟩ := D.property.2 (e.symm x) (e.symm y)
  refine ⟨⟨e.permCongrHom g.val, ⟨g.val, g.property, rfl⟩⟩, ?_⟩
  change e (g.val (e.symm x)) = y
  rw [hg, e.apply_symm_apply]

private theorem localToLabelled_injective (X : Type) [Fintype X] :
    Function.Injective (localToLabelled X) := by
  intro D E h
  apply Subtype.ext
  exact Subgroup.map_injective (Fintype.equivFin X).permCongrHom.injective
    (congrArg Subtype.val h)

/-- Relabelling the original points injects every literal local container
into all labelled transitive groups, also for the empty point type. -/
theorem local_card_le_labelled (X : Type) [Fintype X] :
    Nat.card (LocalContainer X) ≤
      Nat.card (LabelledTransitiveSubgroup (Fintype.card X)) :=
  Nat.card_le_card_of_injective (localToLabelled X) (localToLabelled_injective X)

variable (X : Type) [Fintype X]
local instance : Fintype (Index X) := Fintype.ofFinite _
local instance (label : X → X) (i : X) : Fintype (LocalContainer (Fiber label i)) :=
  Fintype.ofFinite _

theorem local_menu_product_bound
    (ε B : ℝ) (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (hcount : ∀ m, (Nat.card (LabelledTransitiveSubgroup m) : ℝ) ≤
      B * (2 : ℝ) ^ (ε * (m : ℝ) ^ 2)) (label : X → X) :
    (∏ i : X, (Fintype.card (LocalContainer (Fiber label i)) : ℝ)) ≤
      B ^ Fintype.card X * (2 : ℝ) ^ (ε * (Fintype.card X : ℝ) ^ 2) := by
  have hlocal (i : X) :
      (Fintype.card (LocalContainer (Fiber label i)) : ℝ) ≤
        B * (2 : ℝ) ^ (ε * (Fintype.card (Fiber label i) : ℝ) ^ 2) := by
    have hle : (Fintype.card (LocalContainer (Fiber label i)) : ℝ) ≤
        (Nat.card (LabelledTransitiveSubgroup (Fintype.card (Fiber label i))) : ℝ) := by
      have h := local_card_le_labelled (Fiber label i)
      simp only [Nat.card_eq_fintype_card] at h ⊢
      exact_mod_cast h
    exact hle.trans (hcount (Fintype.card (Fiber label i)))
  have hsum : (∑ i : X, (Fintype.card (Fiber label i) : ℝ)) = Fintype.card X := by
    exact_mod_cast fiber_sum X label
  have hsq : (∑ i : X, (Fintype.card (Fiber label i) : ℝ) ^ 2) ≤
      (Fintype.card X : ℝ) ^ 2 := by
    rw [← hsum]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => Nat.cast_nonneg _)
  calc
    _ ≤ ∏ i : X, (B * (2 : ℝ) ^
        (ε * (Fintype.card (Fiber label i) : ℝ) ^ 2)) :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => hlocal i)
    _ = B ^ Fintype.card X * (2 : ℝ) ^
        (ε * ∑ i : X, (Fintype.card (Fiber label i) : ℝ) ^ 2) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        ← Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2), ← Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_left hsq hε)) (pow_nonneg hB _)

/-- Fibre squares use at most the original square-degree budget; labels and
the uniform local coefficient are charged once per original point. -/
theorem index_card_bound
    (ε B : ℝ) (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (hcount : ∀ m, (Nat.card (LabelledTransitiveSubgroup m) : ℝ) ≤
      B * (2 : ℝ) ^ (ε * (m : ℝ) ^ 2)) :
    (Nat.card (Index X) : ℝ) ≤
      (Fintype.card X : ℝ) ^ Fintype.card X *
        (B ^ Fintype.card X * (2 : ℝ) ^ (ε * (Fintype.card X : ℝ) ^ 2)) := by
  change (Nat.card (Σ label : X → X, ∀ i : X, LocalContainer (Fiber label i)) : ℝ) ≤ _
  rw [Nat.card_sigma]
  push_cast
  calc
    _ ≤ ∑ _label : X → X, (B ^ Fintype.card X *
        (2 : ℝ) ^ (ε * (Fintype.card X : ℝ) ^ 2)) := by
      apply Finset.sum_le_sum
      intro label _
      simpa only [Nat.card_eq_fintype_card, Fintype.card_pi, Nat.cast_prod] using
        local_menu_product_bound X ε B hε hB hcount label
    _ = _ := by simp [Fintype.card_fun]

private theorem coefficient_label_cost (B : ℝ) (hB : 0 ≤ B) (b : ℕ) :
    (b : ℝ) ^ b * B ^ b ≤
      (2 : ℝ) ^ boundedWordError (⌈B⌉₊ : ℝ) b 0 := by
  let N := ⌈B⌉₊
  have hN : (N : ℝ) ≤ (2 : ℝ) ^ N := by
    exact_mod_cast (Nat.le_of_lt N.lt_two_pow_self)
  have hbase : B ≤ ((b : ℝ) + 2) ^ N :=
    (Nat.le_ceil B).trans (hN.trans (pow_le_pow_left₀ (by norm_num)
      (by have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b; linarith) _))
  have he : boundedWordError (⌈B⌉₊ : ℝ) b 0 =
      Real.logb 2 ((b : ℝ) + 2) * (((N + 1) * b : ℕ) : ℝ) := by
    unfold boundedWordError Real.logb N
    push_cast
    ring
  rw [he, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_logb (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1) (by positivity), Real.rpow_natCast]
  calc
    _ ≤ ((b : ℝ) + 2) ^ b * (((b : ℝ) + 2) ^ N) ^ b :=
      mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg b) (by linarith) _)
        (pow_le_pow_left₀ hB hbase _) (pow_nonneg hB _) (by positivity)
    _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; ring

/-- This is precisely the weaker logarithmic-scale menu bound required by
the global marked cutoff argument. -/
theorem index_eventually_exp_bound
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ b : ℕ in atTop,
      (Nat.card (Index (Fin b)) : ℝ) ≤ (2 : ℝ) ^ (ε * (b : ℝ) ^ 2) := by
  obtain ⟨B, hB, hcount⟩ := hLMM (ε / 2) (by positivity)
  filter_upwards [boundedWordError_negligible (A := (⌈B⌉₊ : ℝ))
    (Nat.cast_nonneg _) (ε / 2) (by positivity) 0] with b hb
  have herr : boundedWordError (⌈B⌉₊ : ℝ) b 0 ≤ (ε / 2) * (b : ℝ) ^ 2 := by
    simpa only [Nat.cast_zero, add_zero] using hb 0 (by simp)
  have hc := index_card_bound (Fin b) (ε / 2) B (by positivity) hB hcount
  simp only [Fintype.card_fin] at hc
  calc
    (Nat.card (Index (Fin b)) : ℝ) ≤
        ((b : ℝ) ^ b * B ^ b) * (2 : ℝ) ^ ((ε / 2) * (b : ℝ) ^ 2) := by
      simpa only [mul_assoc] using hc
    _ ≤ (2 : ℝ) ^ boundedWordError (⌈B⌉₊ : ℝ) b 0 *
        (2 : ℝ) ^ ((ε / 2) * (b : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (coefficient_label_cost B hB b) (by positivity)
    _ ≤ (2 : ℝ) ^ ((ε / 2) * (b : ℝ) ^ 2) *
        (2 : ℝ) ^ ((ε / 2) * (b : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) herr) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring

end SymmetricSubgroupAsymptotics.MarkedC4.LMMSubquadraticSolubleContainers
