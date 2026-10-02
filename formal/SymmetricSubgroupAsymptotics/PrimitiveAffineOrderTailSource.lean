import SymmetricSubgroupAsymptotics.PrimitiveAffineCyclicSource
import SymmetricSubgroupAsymptotics.Non2PreE7SaprimOddLargeAffine

/-!
# A catalogue-free order-tail source for medium affine degree

For a primitive affine profile the point stabilizer has order at most
`2^((log₂ w + 1)^2)`.  The published permutation-generator bound therefore
counts every quotient of the stabilizer with slope half that logarithmic
square.  From degree `343` onward this slope fits the terminal window.  This
closes every affine profile in degrees `343 ≤ w < 1024`, without a soluble
hypothesis or a finite catalogue.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineOrderTailSource

variable {w : ℕ} {U : PreE7NonPairActionClass w}

def exponent (w : ℕ) : ℕ := (Nat.log 2 w + 1) ^ 2

def tailSlope (w : ℕ) : ℝ := exponent w / 2

/-- Between `343` and `1023`, the logarithmic-square exponent is either
`81` or `100`. -/
theorem exponent_eq_eightyOne_or_hundred
    (hw343 : 343 ≤ w) (hw1024 : w < 1024) :
    exponent w = 81 ∨ exponent w = 100 := by
  have hw0 : w ≠ 0 := by omega
  have hl8 : 8 ≤ Nat.log 2 w := by
    apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
    norm_num
    omega
  have hl10 : Nat.log 2 w < 10 := by
    rw [Nat.log_lt_iff_lt_pow (by norm_num : 1 < 2) hw0]
    norm_num
    exact hw1024
  have : Nat.log 2 w = 8 ∨ Nat.log 2 w = 9 := by omega
  rcases this with h | h
  · left; simp [exponent, h]
  · right; simp [exponent, h]

/-- The order-tail slope fits the common character window throughout the
medium-degree range. -/
theorem tailSlope_window
    (hw343 : 343 ≤ w) (hw1024 : w < 1024) :
    tailSlope w ≤ preE7CharacterWindow w := by
  have hhalfLower : (171 : ℝ) ≤ halfDegree w := by
    exact_mod_cast (show 171 ≤ halfDegree w by
      unfold halfDegree
      omega)
  have hwUpper : (w : ℝ) ≤ 1024 := by exact_mod_cast hw1024.le
  rcases exponent_eq_eightyOne_or_hundred hw343 hw1024 with h | h
  · unfold tailSlope preE7CharacterWindow preE7CharacterRho
    rw [h]
    norm_num
    nlinarith
  · have hlog9 : Nat.log 2 w = 9 := by
      have hw0 : w ≠ 0 := by omega
      have hl8 : 8 ≤ Nat.log 2 w := by
        apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
        norm_num
        omega
      have hl10 : Nat.log 2 w < 10 := by
        rw [Nat.log_lt_iff_lt_pow (by norm_num : 1 < 2) hw0]
        norm_num
        exact hw1024
      interval_cases hl : Nat.log 2 w <;> simp [exponent, hl] at h ⊢
    have hw512 : 512 ≤ w := by
      have hw0 : w ≠ 0 := by omega
      have hp := Nat.pow_log_le_self 2 hw0
      rw [hlog9] at hp
      norm_num at hp
      exact hp
    have hhalf256 : (256 : ℝ) ≤ halfDegree w := by
      exact_mod_cast (show 256 ≤ halfDegree w by
        unfold halfDegree
        omega)
    unfold tailSlope preE7CharacterWindow preE7CharacterRho
    rw [h]
    norm_num
    nlinarith

/-- The generator theorem counts epimorphisms to any target below a
base-two order ceiling with the exact half-logarithmic slope. -/
theorem epi_le_twoPowerCeiling
    (hgen : PermutationSubgroupGeneratorBound)
    {b m : ℕ} (J : Subgroup (Equiv.Perm (Fin b)))
    {Q : Type*} [Group Q] [Finite Q] (hQ : Nat.card Q ≤ 2 ^ m) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      (2 : ℝ) ^ m * (2 : ℝ) ^ (((m : ℝ) / 2) * b) := by
  obtain ⟨T, hT, hTcard⟩ := hgen b J
  have hepi : Nat.card (GroupEpimorphism J Q) ≤ Nat.card (J →* Q) := by
    letI : Finite (J →* Q) := Finite.of_injective
      (fun f : J →* Q => (f : J → Q)) DFunLike.coe_injective
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hnat : Nat.card (GroupEpimorphism J Q) ≤ (2 ^ m) ^ T.card := by
    calc
      Nat.card (GroupEpimorphism J Q) ≤ Nat.card (J →* Q) := hepi
      _ ≤ Nat.card Q ^ T.card := monoidHom_card_le_pow_of_closure T hT
      _ ≤ (2 ^ m) ^ T.card := Nat.pow_le_pow_left hQ _
  have hexp : (m : ℝ) * T.card ≤ m + ((m : ℝ) / 2) * b := by
    have hTcardR : (2 : ℝ) * T.card ≤ b + 2 := by exact_mod_cast hTcard
    have hm : (0 : ℝ) ≤ m := by positivity
    nlinarith
  calc
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
        (((2 ^ m) ^ T.card : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = (2 : ℝ) ^ ((m : ℝ) * T.card) := by
      rw [← pow_mul, Nat.cast_pow, Nat.cast_ofNat, ← Nat.cast_mul,
        Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ ((m : ℝ) + ((m : ℝ) / 2) * b) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = _ := by rw [Real.rpow_add (by norm_num), Real.rpow_natCast]

/-- Every normal axis is a pure tail.  The bottom and all point-stabilizer
quotients use the same logarithmic-square order ceiling. -/
def axis
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw343 : 343 ≤ w)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w)
    (hgen : PermutationSubgroupGeneratorBound)
    (N : {N : Subgroup (preE7NonPairAction w U) // N.Normal}) :
    PreE7SmallAxisCertificate (preE7NonPairAction w U) N PUnit
      (tailSlope w) := by
  letI : Nontrivial (Fin w) := Fin.nontrivial_iff_two_le.mpr (by omega)
  haveI : N.1.Normal := N.2
  by_cases hN : N.1 = ⊥
  · refine .tail ((2 : ℝ) ^ exponent w) (by positivity) ?_
    intro b J
    let e : (preE7NonPairAction w U ⧸ N.1) ≃*
        preE7NonPairAction w U :=
      (QuotientGroup.quotientMulEquivOfEq hN).trans QuotientGroup.quotientBot
    rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e]
    apply epi_le_twoPowerCeiling hgen J
    simpa [exponent] using P.card_le_two_pow_logSquare x
  · refine .tail ((2 : ℝ) ^ exponent w) (by positivity) ?_
    intro b J
    have hVle : P.V ≤ N.1 :=
      le_of_minimal_selfCentralizing P.V (P.minimal hprimitive)
        (P.selfCentralizing hprimitive) N.1 hN
    have hker : (P.complementProjection x).ker ≤ N.1 := by
      rw [P.complementProjection_ker x]
      exact hVle
    let M : Subgroup (P.complement x) :=
      N.1.map (P.complementProjection x)
    haveI hM : M.Normal := N.2.map _ (P.complementProjection_surjective x)
    let e : (preE7NonPairAction w U ⧸ N.1) ≃* (P.complement x ⧸ M) :=
      quotientEquivOfKerLe (P.complementProjection x)
        (P.complementProjection_surjective x) N.1 hker
    rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e]
    apply epi_le_twoPowerCeiling hgen J
    calc
      Nat.card (P.complement x ⧸ M) ≤ Nat.card (P.complement x) :=
        Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective (s := M))
      _ ≤ Nat.card (preE7NonPairAction w U) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ ≤ 2 ^ exponent w := by
        simpa [exponent] using P.card_le_two_pow_logSquare x

private theorem axis_mainCoefficient
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw343 : 343 ≤ w)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w)
    (hgen : PermutationSubgroupGeneratorBound)
    (N : {N : Subgroup (preE7NonPairAction w U) // N.Normal}) :
    (axis P hw343 hprimitive x hgen N).mainCoefficient = 0 := by
  by_cases hN : N.1 = ⊥ <;>
    simp [axis, hN, PreE7SmallAxisCertificate.mainCoefficient]

private theorem axis_tailCoefficient_le
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw343 : 343 ≤ w)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w)
    (hgen : PermutationSubgroupGeneratorBound)
    (N : {N : Subgroup (preE7NonPairAction w U) // N.Normal}) :
    (axis P hw343 hprimitive x hgen N).tailCoefficient ≤
      (2 : ℝ) ^ exponent w := by
  by_cases hN : N.1 = ⊥ <;>
    simp [axis, hN, PreE7SmallAxisCertificate.tailCoefficient]

def toData
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw343 : 343 ≤ w) (hw1024 : w < 1024)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w)
    (hgen : PermutationSubgroupGeneratorBound) :
    PreE7SmallAdditiveData w U where
  R := PUnit
  degree := 0
  action := 1
  action_injective := fun _ _ _ => Subsingleton.elim _ _
  tailSlope := tailSlope w
  comparator_window := trivialSmallComparatorWindow (by omega)
  tail_window := tailSlope_window hw343 hw1024
  axis := axis P hw343 hprimitive x hgen

private theorem menu_exponent
    (hw343 : 343 ≤ w) (hw1024 : w < 1024) :
    exponent w * exponent w + exponent w + 1 ≤ 64 * w := by
  rcases exponent_eq_eightyOne_or_hundred hw343 hw1024 with h | h
  · rw [h]
    omega
  · rw [h]
    omega

private theorem coefficient_menu
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw343 : 343 ≤ w) (hw1024 : w < 1024) (x : Fin w) (b : ℕ) :
    (Nat.card {N : Subgroup (preE7NonPairAction w U) // N.Normal} : ℝ) *
          (2 : ℝ) ^ exponent w ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  let m := exponent w
  have horder : Nat.card (preE7NonPairAction w U) ≤ 2 ^ m := by
    simpa [m, exponent] using P.card_le_two_pow_logSquare x
  have hnormal :
      Nat.card {N : Subgroup (preE7NonPairAction w U) // N.Normal} ≤
        2 ^ (m * m) := normalSubgroup_card_le_two_pow_sq m horder
  have hnat :
      Nat.card {N : Subgroup (preE7NonPairAction w U) // N.Normal} * 2 ^ m ≤
        2 ^ (m * m + m + 1) := by
    calc
      _ ≤ 2 ^ (m * m) * 2 ^ m := Nat.mul_le_mul_right _ hnormal
      _ = 2 ^ (m * m + m) := by rw [pow_add]
      _ ≤ 2 ^ (m * m + m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hexp : m * m + m + 1 ≤ 64 * w := by
    simpa [m] using menu_exponent hw343 hw1024
  calc
    _ ≤ ((2 ^ (m * m + m + 1) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    _ = (2 : ℝ) ^ ((m * m + m + 1 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      norm_num
    _ ≤ (2 : ℝ) ^ (64 * (w : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact_mod_cast hexp
    _ ≤ _ := two_rpow_sixtyFour_width_le_menuMass (by omega) b

noncomputable def numericalData
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw343 : 343 ≤ w) (hw1024 : w < 1024)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w)
    (hgen : PermutationSubgroupGeneratorBound) :
    PreE7SmallAdditiveNumericalData .saprim w U where
  data := toData P hw343 hw1024 hprimitive x hgen
  main_total_bound := by
    intro b
    have hz : fusionAxisEnvelopeTotal (preE7NonPairAction w U)
        (fun N => ((toData P hw343 hw1024 hprimitive x hgen).certificate
          .saprim).C b N) = 0 := by
      unfold fusionAxisEnvelopeTotal
      apply Finset.sum_eq_zero
      intro N _
      exact axis_mainCoefficient P hw343 hprimitive x hgen N
    rw [hz]
    exact Real.rpow_nonneg (by norm_num) _
  tail_total_bound := by
    intro b
    calc
      fusionAxisEnvelopeTotal (preE7NonPairAction w U)
          (fun N => ((toData P hw343 hw1024 hprimitive x hgen).certificate
            .saprim).tailCoefficient b N) ≤
          fusionAxisEnvelopeTotal (preE7NonPairAction w U)
            (fun _N => (2 : ℝ) ^ exponent w) := by
        unfold fusionAxisEnvelopeTotal
        apply Finset.sum_le_sum
        intro N _
        exact axis_tailCoefficient_le P hw343 hprimitive x hgen N
      _ = (Nat.card {N : Subgroup (preE7NonPairAction w U) // N.Normal} : ℝ) *
            (2 : ℝ) ^ exponent w := by
        unfold fusionAxisEnvelopeTotal
        simp [Finset.sum_const, nsmul_eq_mul]
        exact @Fintype.card_congr
          {N : Subgroup (preE7NonPairAction w U) // N.Normal}
          {N : Subgroup (preE7NonPairAction w U) // N.Normal}
          (Subtype.fintype Subgroup.Normal) originalNormalFintype (Equiv.refl _)
      _ ≤ _ := coefficient_menu P hw343 hw1024 x b

/-- Every primitive affine profile in the medium range supplies a concrete
SAPRIM source, with no structural hypothesis on the complement. -/
noncomputable def toRankTailOwnerSource
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw343 : 343 ≤ w) (hw1024 : w < 1024)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w)
    (hgen : PermutationSubgroupGeneratorBound) :
    PreE7RankTailOwnerSourceData w U :=
  .ordinary .saprim (.small
    (numericalData P hw343 hw1024 hprimitive x hgen))

end PrimitiveAffineOrderTailSource
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
