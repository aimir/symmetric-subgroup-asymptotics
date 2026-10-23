import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckFixedCoordinateCardinality
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveCardinality
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootGeneratedPGroup

/-! The genuine identity-field-twist fixed D4 positive group has q^6
members. The five actual height kernels contribute q^2,q,q,q,q.
No exceptional group-order formula is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckFixedPositiveCardinality
open CFSGGTwoD4GeckFixedCoordinateCardinality
open CFSGTrialityGeckFixedPositiveCardinality CFSGTrialityGeckFixedTailCardinality
open CFSGTrialityGeckFixedPositiveGeneration CFSGTrialityGeckFixedCoordinateDecomposition
open CFSGTrialityGeckRootGeneratedPGroup CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckPositiveTwist CFSGTrialityGeckMatrixTwist

theorem coordinates_card_one (K : Type) [Field K] [Finite K] :
    Nat.card (fixedCoordinates K (RingEquiv.refl K) 1) = (Nat.card K) ^ 2 := by
  have hl : Nat.card (LongAt (1:ℤ)) = 1 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hs : Nat.card (ShortAt (1:ℤ)) = 1 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [fixedCoordinates_card,hl,hs]

theorem coordinates_card_two (K : Type) [Field K] [Finite K] :
    Nat.card (fixedCoordinates K (RingEquiv.refl K) 2) = (Nat.card K) := by
  have hl : Nat.card (LongAt (2:ℤ)) = 0 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hs : Nat.card (ShortAt (2:ℤ)) = 1 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [fixedCoordinates_card,hl,hs]
  norm_num

theorem coordinates_card_three (K : Type) [Field K] [Finite K] :
    Nat.card (fixedCoordinates K (RingEquiv.refl K) 3) = (Nat.card K) := by
  have hl : Nat.card (LongAt (3:ℤ)) = 0 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hs : Nat.card (ShortAt (3:ℤ)) = 1 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [fixedCoordinates_card,hl,hs]
  norm_num

theorem coordinates_card_four (K : Type) [Field K] [Finite K] :
    Nat.card (fixedCoordinates K (RingEquiv.refl K) 4) = (Nat.card K) := by
  have hl : Nat.card (LongAt (4:ℤ)) = 1 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hs : Nat.card (ShortAt (4:ℤ)) = 0 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [fixedCoordinates_card,hl,hs]
  norm_num

theorem coordinates_card_five (K : Type) [Field K] [Finite K] :
    Nat.card (fixedCoordinates K (RingEquiv.refl K) 5) = (Nat.card K) := by
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

theorem fixedPositive_card (K : Type) [Field K] [Finite K] :
    Nat.card (fixedPositive K (RingEquiv.refl K)) = (Nat.card K) ^ 6 := by
  let a : ℤ → ℕ := fun h => Nat.card
    (fixedTail K (RingEquiv.refl K) h)
  let c : ℤ → ℕ := fun h => Nat.card
    (fixedCoordinates K (RingEquiv.refl K) h)
  have hs (h : ℤ) (hh : 0 < h) : a h = c h * a (h+1) :=
    fixedTail_card_step K (RingEquiv.refl K) h hh
  have hp : Nat.card (fixedPositive K (RingEquiv.refl K)) = a 1 :=
    (Nat.card_congr (MulEquiv.subgroupCongr
      (fixedTail_one_eq K (RingEquiv.refl K))).toEquiv).symm
  have h6 : a 6 = 1 := by
    simpa only [Subgroup.card_bot] using Nat.card_congr (MulEquiv.subgroupCongr
      (fixedTail_six_eq_bot K (RingEquiv.refl K))).toEquiv
  have hc1 : c 1 = (Nat.card K)^2 := coordinates_card_one K
  have hc2 : c 2 = (Nat.card K) := coordinates_card_two K
  have hc3 : c 3 = (Nat.card K) := coordinates_card_three K
  have hc4 : c 4 = (Nat.card K) := coordinates_card_four K
  have hc5 : c 5 = (Nat.card K) := coordinates_card_five K
  have he := five_step_product a c hs
  rw [h6,hc1,hc2,hc3,hc4,hc5] at he
  exact hp.trans (he.trans (by ring))


def rootPartEquivFixedPositive (K : Type) [Field K] [Finite K] (sigma : K≃+*K) :
    rootPart K sigma false≃*fixedPositive K sigma where
  toFun x := ⟨⟨x.val.val,x.property.1⟩,by
    apply Subtype.ext
    exact x.property.2⟩
  invFun u := ⟨⟨u.val.val,signedFixed_le_generated K sigma false ⟨u.val.property,by
    have he := congrArg (fun z : Positive K=>z.val) u.property
    change unitTwist K sigma u.val.val=u.val.val at he
    exact he⟩⟩,u.val.property,by
      have he := congrArg (fun z : Positive K=>z.val) u.property
      change unitTwist K sigma u.val.val=u.val.val at he
      exact he⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem rootPart_card (K : Type) [Field K] [Finite K] :
    Nat.card (rootPart K (RingEquiv.refl K) false)=Nat.card K^6 := by
  rw [Nat.card_congr (rootPartEquivFixedPositive K (RingEquiv.refl K)).toEquiv]
  exact fixedPositive_card K

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckFixedPositiveCardinality
