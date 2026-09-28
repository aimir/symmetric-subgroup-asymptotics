import SymmetricSubgroupAsymptotics.GrowingQuotientDegreeBounds

/-!
# Controlled padding of a growing comparator action

The manuscript pads a faithful comparator action by fixed points before
choosing its moment.  This file verifies the numerical part of that operation
with the parity-safe even width retained exactly.  A nontrivial original
comparator supplies the additional lower bound needed for the graph-degree
estimates; the trivial comparator is handled separately.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- The largest even integer at most `w`. -/
def evenWidth (w : ℕ) : ℕ := 2 * halfDegree w

theorem evenWidth_le (w : ℕ) : evenWidth w ≤ w := by
  unfold evenWidth halfDegree
  omega

theorem width_le_evenWidth_add_one (w : ℕ) : w ≤ evenWidth w + 1 := by
  unfold evenWidth halfDegree
  omega

/-- Pad the given faithful degree by fixed points up to the controlled floor
used in the growing transfer theorem. -/
def paddedComparatorDegree (ρ : ℝ) (v₀ w : ℕ) : ℕ :=
  max v₀ ⌊4 * ρ * (evenWidth w : ℝ)⌋₊

/-- The residual margin after padding. -/
def paddedComparatorDelta (ρ η : ℝ) (v₀ w : ℕ) : ℝ :=
  ((evenWidth w : ℝ) - paddedComparatorDegree ρ v₀ w) / 8 - η

/-- Padding stays strictly below the original width by a uniform fraction. -/
theorem paddedComparatorDegree_upper
    {ρ η : ℝ} {v₀ w : ℕ}
    (hρ : 0 < ρ) (hη : 0 ≤ η)
    (hmargin : ρ * w ≤ ((evenWidth w : ℝ) - v₀) / 8 - η) :
    (paddedComparatorDegree ρ v₀ w : ℝ) ≤ (1 - 4 * ρ) * w := by
  let x : ℝ := 4 * ρ * (evenWidth w : ℝ)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hew : (evenWidth w : ℝ) ≤ w := by exact_mod_cast evenWidth_le w
  have hv₀ : (v₀ : ℝ) ≤ (1 - 4 * ρ) * w := by
    nlinarith
  have hfloor : (⌊x⌋₊ : ℝ) ≤ (1 - 4 * ρ) * w := by
    have hfx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
    have hxw : x ≤ 4 * ρ * w := by
      dsimp [x]
      exact mul_le_mul_of_nonneg_left hew (by positivity)
    nlinarith
  unfold paddedComparatorDegree
  rw [Nat.cast_max]
  exact max_le hv₀ hfloor

/-- At most half of the original margin is lost to padding. -/
theorem paddedComparatorDelta_lower
    {ρ η : ℝ} {v₀ w : ℕ}
    (hρ : 0 < ρ)
    (hmargin : ρ * w ≤ ((evenWidth w : ℝ) - v₀) / 8 - η) :
    ρ * w / 2 ≤ paddedComparatorDelta ρ η v₀ w := by
  let x : ℝ := 4 * ρ * (evenWidth w : ℝ)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hv : (paddedComparatorDegree ρ v₀ w : ℝ) ≤ (v₀ : ℝ) + x := by
    unfold paddedComparatorDegree
    rw [Nat.cast_max]
    apply max_le
    · linarith
    · linarith [show (0 : ℝ) ≤ v₀ by positivity]
  have hew : (evenWidth w : ℝ) ≤ w := by exact_mod_cast evenWidth_le w
  unfold paddedComparatorDelta
  dsimp [x] at hv
  nlinarith [mul_nonneg hρ.le (sub_nonneg.mpr hew)]

/-- A nontrivial faithful comparator remains linearly large after padding.
The small `ρ*w` case uses the original two-point lower bound; otherwise the
floor term itself is larger than `ρ*w`. -/
theorem paddedComparatorDegree_lower_of_two_le
    {ρ : ℝ} {v₀ w : ℕ}
    (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8) (hv₀ : 2 ≤ v₀) :
    ρ * w ≤ (paddedComparatorDegree ρ v₀ w : ℝ) := by
  let x : ℝ := 4 * ρ * (evenWidth w : ℝ)
  have hmax₀ : (v₀ : ℝ) ≤ paddedComparatorDegree ρ v₀ w := by
    exact_mod_cast le_max_left v₀ ⌊x⌋₊
  have hmaxFloor : (⌊x⌋₊ : ℝ) ≤ paddedComparatorDegree ρ v₀ w := by
    exact_mod_cast le_max_right v₀ ⌊x⌋₊
  by_cases hsmall : ρ * w ≤ 1
  · have hv₂ : (2 : ℝ) ≤ v₀ := by exact_mod_cast hv₀
    linarith
  · have hew : (w : ℝ) ≤ evenWidth w + 1 := by
      exact_mod_cast width_le_evenWidth_add_one w
    have hfloor := Nat.lt_floor_add_one x
    have hx : ρ * w + 1 ≤ x := by
      dsimp [x]
      nlinarith
    have hρwFloor : ρ * w ≤ (⌊x⌋₊ : ℝ) := by
      nlinarith
    exact hρwFloor.trans hmaxFloor

/-- The three numerical hypotheses consumed by the nontrivial hot theorem
are all consequences of the original margin and controlled padding. -/
theorem paddedComparator_parameters
    {ρ η : ℝ} {v₀ w : ℕ}
    (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8) (hη : 0 ≤ η)
    (hv₀ : 2 ≤ v₀)
    (hmargin : ρ * w ≤ ((evenWidth w : ℝ) - v₀) / 8 - η) :
    let v := paddedComparatorDegree ρ v₀ w
    let δ := paddedComparatorDelta ρ η v₀ w
    ρ * w ≤ (v : ℝ) ∧
      (v : ℝ) ≤ (1 - 4 * ρ) * w ∧
        ρ * w / 2 ≤ δ := by
  dsimp
  exact ⟨paddedComparatorDegree_lower_of_two_le hρ hρ8 hv₀,
    paddedComparatorDegree_upper hρ hη hmargin,
    paddedComparatorDelta_lower hρ hmargin⟩

end SymmetricSubgroupAsymptotics

end
