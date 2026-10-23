import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedCoordinateCardinality

/-! The literal triality-fixed positive matrix group has exactly q^12
members. Five actual height kernels contribute q^4,q^3,q^3,q,q. This
counts fixed coordinates, not a supplied exceptional group-order formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveCardinality
open CFSGTrialityGeckFixedTailCardinality CFSGTrialityGeckFixedCoordinateCardinality
open CFSGTrialityGeckFixedPositiveGeneration CFSGTrialityGeckFixedCoordinateDecomposition
open CFSGTrialityGeckWordRootIndex CFSGTrialityGeckSectionRootLabels
open CFSGTrialityD4PositiveRootOrbits CFSGTrialityD4PositiveRootIndex
open CFSGTrialityGeckHeightQuotientTwist
open CFSGTrialityD4NormTwo CFSGTrialityGeckPositiveTwist CFSGSerreOrdinaryTwists
open CFSGNormTwoCoordinateRootHeightFiltration CFSGIntegerHeightSign

private theorem positive_height_le_five (k : CFSGTrialityD4PositiveRootIndex.Positive) :
    height k.val.val ≤ 5 := by
  obtain ⟨a,rfl⟩ := wordPositiveRootEquiv.surjective k
  rcases a with s | ⟨s,k⟩
  · change height (longRoot s).val ≤ 5
    change (∑ i, (longRoot s).val i) ≤ 5
    rw [long_height]
    fin_cases s <;> norm_num
  · change height (shortLabel s k).val ≤ 5
    rw [short_label_height]
    fin_cases s <;> norm_num

theorem tail_six_eq_bot (K : Type) [Field K] : TailInPositive K 6 = ⊥ := by
  have hb : heightTail (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite
      (CartanMatrix.D_off_diag_nonpos 4) K 6 = ⊥ := by
    apply bot_unique
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨k,hk,a,rfl⟩
    have hh := positive_height_le_five k
    omega
  change (heightTail (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite
    (CartanMatrix.D_off_diag_nonpos 4) K 6).subgroupOf (Positive K) = ⊥
  rw [hb,Subgroup.bot_subgroupOf]

theorem fixedTail_six_eq_bot (K : Type) [Field K] [Finite K] (sigma : K ≃+* K) :
    fixedTail K sigma 6 = ⊥ := by
  rw [fixedTail,tail_six_eq_bot]
  exact le_antisymm inf_le_left bot_le

theorem fixedTail_one_eq (K : Type) [Field K] [Finite K] (sigma : K ≃+* K) :
    fixedTail K sigma 1 = fixedPositive K sigma := by
  rw [fixedTail,first_tail_eq_top]
  exact le_antisymm inf_le_right (le_inf le_top le_rfl)

theorem coordinates_card_one (q : CFSG.PrimePower) :
    Nat.card (fixedCoordinates (q.Extension 3) (definingFieldAutomorphism q 3) 1) = q.order ^ 4 := by
  have hl : Nat.card (LongAt (1:ℤ)) = 1 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hs : Nat.card (ShortAt (1:ℤ)) = 1 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [fixedCoordinates_card,hl,hs]

theorem coordinates_card_two (q : CFSG.PrimePower) :
    Nat.card (fixedCoordinates (q.Extension 3) (definingFieldAutomorphism q 3) 2) = q.order ^ 3 := by
  have hl : Nat.card (LongAt (2:ℤ)) = 0 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hs : Nat.card (ShortAt (2:ℤ)) = 1 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [fixedCoordinates_card,hl,hs]

theorem coordinates_card_three (q : CFSG.PrimePower) :
    Nat.card (fixedCoordinates (q.Extension 3) (definingFieldAutomorphism q 3) 3) = q.order ^ 3 := by
  have hl : Nat.card (LongAt (3:ℤ)) = 0 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hs : Nat.card (ShortAt (3:ℤ)) = 1 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [fixedCoordinates_card,hl,hs]

theorem coordinates_card_four (q : CFSG.PrimePower) :
    Nat.card (fixedCoordinates (q.Extension 3) (definingFieldAutomorphism q 3) 4) = q.order := by
  have hl : Nat.card (LongAt (4:ℤ)) = 1 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hs : Nat.card (ShortAt (4:ℤ)) = 0 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [fixedCoordinates_card,hl,hs]
  norm_num

theorem coordinates_card_five (q : CFSG.PrimePower) :
    Nat.card (fixedCoordinates (q.Extension 3) (definingFieldAutomorphism q 3) 5) = q.order := by
  have hl : Nat.card (LongAt (5:ℤ)) = 1 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hs : Nat.card (ShortAt (5:ℤ)) = 0 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [fixedCoordinates_card,hl,hs]
  norm_num

private theorem five_step_product (a c : ℤ → ℕ)
    (h : ∀ i : ℤ,0 < i → a i = c i * a (i+1)) :
    a 1 = c 1 * (c 2 * (c 3 * (c 4 * (c 5 * a 6)))) := by
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  have h4 := h 4 (by decide)
  have h5 := h 5 (by decide)
  norm_num only at h1 h2 h3 h4 h5
  rw [h1,h2,h3,h4,h5]

theorem fixedPositive_card (q : CFSG.PrimePower) :
    Nat.card (fixedPositive (q.Extension 3) (definingFieldAutomorphism q 3)) = q.order ^ 12 := by
  let a : ℤ → ℕ := fun h => Nat.card
    (fixedTail (q.Extension 3) (definingFieldAutomorphism q 3) h)
  let c : ℤ → ℕ := fun h => Nat.card
    (fixedCoordinates (q.Extension 3) (definingFieldAutomorphism q 3) h)
  have hs (h : ℤ) (hh : 0 < h) : a h = c h * a (h+1) :=
    fixedTail_card_step (q.Extension 3) (definingFieldAutomorphism q 3) h hh
  have hp : Nat.card (fixedPositive (q.Extension 3) (definingFieldAutomorphism q 3)) = a 1 :=
    (Nat.card_congr (MulEquiv.subgroupCongr
      (fixedTail_one_eq (q.Extension 3) (definingFieldAutomorphism q 3))).toEquiv).symm
  have h6 : a 6 = 1 := by
    simpa only [Subgroup.card_bot] using Nat.card_congr (MulEquiv.subgroupCongr
      (fixedTail_six_eq_bot (q.Extension 3) (definingFieldAutomorphism q 3))).toEquiv
  have hc1 : c 1 = q.order^4 := coordinates_card_one q
  have hc2 : c 2 = q.order^3 := coordinates_card_two q
  have hc3 : c 3 = q.order^3 := coordinates_card_three q
  have hc4 : c 4 = q.order := coordinates_card_four q
  have hc5 : c 5 = q.order := coordinates_card_five q
  have he := five_step_product a c hs
  rw [h6,hc1,hc2,hc3,hc4,hc5] at he
  exact hp.trans (he.trans (by ring))

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveCardinality
