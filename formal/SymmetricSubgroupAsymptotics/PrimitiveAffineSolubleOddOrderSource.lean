import SymmetricSubgroupAsymptotics.PrimitiveAffineSolubleSource
import SymmetricSubgroupAsymptotics.Non2PreE7SaprimOddLargeAffine
import SymmetricSubgroupAsymptotics.PrimitiveAffineDimensionOrderTailSource

/-!
# Exact-order tails for soluble odd primitive-affine profiles

At degrees `27`, `49` and `81`, the published solvable primitive-linear
order bounds fit the physical window without rounding the complement order
to a power of two.  This file proves the complete normal-axis source from a
literal `PrimitiveAffineProfile`; only the three published order bounds are
inputs.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineSolubleOddOrderSource

variable {w : ℕ} {U : PreE7NonPairActionClass w}

def tailSlope (q : ℕ) : ℝ := Real.logb 2 q / 2

private theorem bottom_epi_le
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw : 6 ≤ w)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (D : SolubleDerivedLength (P.complement x))
    {q : ℕ} (hq : 3 ≤ q) {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (preE7NonPairAction w U)) : ℝ) ≤
      (Nat.card (preE7NonPairAction w U ≃* preE7NonPairAction w U) : ℝ) *
        (2 : ℝ) ^ (tailSlope q * b) := by
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  letI : Nontrivial (Fin w) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h := (P.derivedCyclicTarget hprimitive x D).epi_card_le_prime J
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg b)
  calc
    Real.logb 2 P.p / P.p ≤ Real.logb 2 3 / 3 :=
      PrimitiveAffineSolubleSource.primitiveAffine_primeSlope_le_common P
    _ ≤ Real.logb 2 q / 2 := logThreeThird_le_logHalf hq

/-- Every literal normal axis is a pure exact-order tail.  The bottom uses
the derived affine target; all nonbottom quotients are quotients of the
literal point stabilizer. -/
def axis
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw : 6 ≤ w)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (D : SolubleDerivedLength (P.complement x))
    (hgen : PermutationSubgroupGeneratorBound)
    {q : ℕ} (hq : 3 ≤ q) (horder : Nat.card (P.complement x) ≤ q)
    (N : {N : Subgroup (preE7NonPairAction w U) // N.Normal}) :
    PreE7SmallAxisCertificate (preE7NonPairAction w U) N PUnit
      (tailSlope q) := by
  letI : Nontrivial (Fin w) := Fin.nontrivial_iff_two_le.mpr (by omega)
  haveI : N.1.Normal := N.2
  by_cases hN : N.1 = ⊥
  · refine .tail
      (Nat.card (preE7NonPairAction w U ≃* preE7NonPairAction w U))
      (Nat.cast_nonneg _) ?_
    intro b J
    let e : (preE7NonPairAction w U ⧸ N.1) ≃*
        preE7NonPairAction w U :=
      (QuotientGroup.quotientMulEquivOfEq hN).trans
        QuotientGroup.quotientBot
    rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e]
    exact bottom_epi_le P hw hprimitive x D hq J
  · refine .tail q (Nat.cast_nonneg _) ?_
    intro b J
    have hVle : P.V ≤ N.1 :=
      le_of_minimal_selfCentralizing P.V (P.minimal hprimitive)
        (P.selfCentralizing hprimitive) N.1 hN
    have hker : (P.complementProjection x).ker ≤ N.1 := by
      rw [P.complementProjection_ker x]
      exact hVle
    let M : Subgroup (P.complement x) :=
      N.1.map (P.complementProjection x)
    haveI hM : M.Normal :=
      N.2.map _ (P.complementProjection_surjective x)
    let e : (preE7NonPairAction w U ⧸ N.1) ≃* (P.complement x ⧸ M) :=
      quotientEquivOfKerLe (P.complementProjection x)
        (P.complementProjection_surjective x) N.1 hker
    rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e]
    apply PreE7SaprimOddLargeAffineSource.epi_le_orderCeiling
      hgen J (by omega : 1 ≤ q)
    exact (Nat.card_le_card_of_surjective _
      (QuotientGroup.mk_surjective (s := M))).trans horder

private theorem axis_mainCoefficient
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw : 6 ≤ w)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (D : SolubleDerivedLength (P.complement x))
    (hgen : PermutationSubgroupGeneratorBound)
    {q : ℕ} (hq : 3 ≤ q) (horder : Nat.card (P.complement x) ≤ q)
    (N : {N : Subgroup (preE7NonPairAction w U) // N.Normal}) :
    (axis P hw hprimitive x D hgen hq horder N).mainCoefficient = 0 := by
  by_cases hN : N.1 = ⊥ <;>
    simp [axis, hN, PreE7SmallAxisCertificate.mainCoefficient]

private theorem axis_tailCoefficient_le
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw : 6 ≤ w)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (D : SolubleDerivedLength (P.complement x))
    (hgen : PermutationSubgroupGeneratorBound)
    {q : ℕ} (hq : 3 ≤ q) (horder : Nat.card (P.complement x) ≤ q)
    (N : {N : Subgroup (preE7NonPairAction w U) // N.Normal}) :
    (axis P hw hprimitive x D hgen hq horder N).tailCoefficient ≤
      (if N.1 = ⊥ then
        (Nat.card (preE7NonPairAction w U ≃* preE7NonPairAction w U) : ℝ)
      else 0) + q := by
  by_cases hN : N.1 = ⊥ <;>
    simp [axis, hN, PreE7SmallAxisCertificate.tailCoefficient]

def toData
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw : 6 ≤ w)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (D : SolubleDerivedLength (P.complement x))
    (hgen : PermutationSubgroupGeneratorBound)
    {q : ℕ} (hq : 3 ≤ q) (horder : Nat.card (P.complement x) ≤ q)
    (hwindow : tailSlope q ≤ preE7CharacterWindow w) :
    PreE7SmallAdditiveData w U where
  R := PUnit
  degree := 0
  action := 1
  action_injective := fun _ _ _ => Subsingleton.elim _ _
  tailSlope := tailSlope q
  comparator_window := trivialSmallComparatorWindow hw
  tail_window := hwindow
  axis := axis P hw hprimitive x D hgen hq horder

private theorem small_menu_exponent
    (hw : 27 ≤ w) (hw1024 : w < 1024) :
    let m := (Nat.log 2 w + 1) ^ 2
    m * m + m + 1 ≤ 64 * w := by
  dsimp
  have hw0 : w ≠ 0 := by omega
  have hl4 : 4 ≤ Nat.log 2 w := by
    apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
    norm_num
    omega
  have hl10 : Nat.log 2 w < 10 := by
    rw [Nat.log_lt_iff_lt_pow (by norm_num : 1 < 2) hw0]
    norm_num
    exact hw1024
  have hpow : 2 ^ Nat.log 2 w ≤ w := Nat.pow_log_le_self 2 hw0
  interval_cases hlog : Nat.log 2 w <;> norm_num [hlog] at hpow ⊢ <;> omega

private theorem coefficient_menu
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (hw : 27 ≤ w) (hw1024 : w < 1024)
    {q b : ℕ}
    (hq : q ≤ 2 ^ ((Nat.log 2 w + 1) ^ 2)) :
    (Nat.card (preE7NonPairAction w U ≃* preE7NonPairAction w U) : ℝ) +
        (Nat.card {N : Subgroup (preE7NonPairAction w U) // N.Normal} : ℝ) * q ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  let m := (Nat.log 2 w + 1) ^ 2
  have hU : Nat.card (preE7NonPairAction w U) ≤ 2 ^ m := by
    simpa [m] using P.card_le_two_pow_logSquare x
  have hq' : q ≤ 2 ^ m := by simpa [m] using hq
  have hnormal :
      Nat.card {N : Subgroup (preE7NonPairAction w U) // N.Normal} ≤
        2 ^ (m * m) := normalSubgroup_card_le_two_pow_sq m hU
  have haut : Nat.card (preE7NonPairAction w U ≃*
      preE7NonPairAction w U) ≤ 2 ^ (m * m) := by
    calc
      Nat.card (preE7NonPairAction w U ≃* preE7NonPairAction w U) ≤
          Nat.card (preE7NonPairAction w U) ^
            Nat.log 2 (Nat.card (preE7NonPairAction w U)) :=
        mulEquiv_card_le_card_pow_log _
      _ ≤ (2 ^ m) ^ Nat.log 2 (Nat.card (preE7NonPairAction w U)) :=
        Nat.pow_le_pow_left hU _
      _ ≤ (2 ^ m) ^ m := by
        apply Nat.pow_le_pow_right (by positivity)
        exact (Nat.log_mono_right (b := 2) hU).trans_eq
          (Nat.log_pow (by norm_num) m)
      _ = 2 ^ (m * m) := by rw [pow_mul]
  have hnat :
      Nat.card (preE7NonPairAction w U ≃* preE7NonPairAction w U) +
          Nat.card {N : Subgroup (preE7NonPairAction w U) // N.Normal} * q ≤
        2 ^ (m * m + m + 1) := by
    have hmul : 2 ^ (m * m) * 2 ^ m = 2 ^ (m * m + m) := by
      rw [pow_add]
    calc
      _ ≤ 2 ^ (m * m) + 2 ^ (m * m) * 2 ^ m :=
        Nat.add_le_add haut (Nat.mul_le_mul hnormal hq')
      _ ≤ 2 ^ (m * m + m) + 2 ^ (m * m + m) := by
        rw [hmul]
        exact Nat.add_le_add
          (Nat.pow_le_pow_right (by norm_num) (by omega)) le_rfl
      _ = 2 ^ (m * m + m + 1) := by rw [pow_succ]; omega
  have hexp : m * m + m + 1 ≤ 64 * w := by
    simpa [m] using small_menu_exponent hw hw1024
  calc
    _ ≤ ((2 ^ (m * m + m + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = (2 : ℝ) ^ ((m * m + m + 1 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      norm_num
    _ ≤ (2 : ℝ) ^ (64 * (w : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact_mod_cast hexp
    _ ≤ _ := two_rpow_sixtyFour_width_le_menuMass (by omega) b

noncomputable def numericalData
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw : 27 ≤ w) (hw1024 : w < 1024)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (D : SolubleDerivedLength (P.complement x))
    (hgen : PermutationSubgroupGeneratorBound)
    {q : ℕ} (hq : 3 ≤ q) (horder : Nat.card (P.complement x) ≤ q)
    (hqBound : q ≤ 2 ^ ((Nat.log 2 w + 1) ^ 2))
    (hwindow : tailSlope q ≤ preE7CharacterWindow w) :
    PreE7SmallAdditiveNumericalData .saprim w U where
  data := toData P (by omega) hprimitive x D hgen hq horder hwindow
  main_total_bound := by
    intro b
    have hz : fusionAxisEnvelopeTotal (preE7NonPairAction w U)
        (fun N =>
          ((toData P (by omega) hprimitive x D hgen hq horder hwindow).certificate
            .saprim).C b N) = 0 := by
      unfold fusionAxisEnvelopeTotal
      apply Finset.sum_eq_zero
      intro N _
      exact axis_mainCoefficient P (by omega) hprimitive x D hgen hq horder N
    rw [hz]
    exact Real.rpow_nonneg (by norm_num) _
  tail_total_bound := by
    intro b
    let B : {N : Subgroup (preE7NonPairAction w U) // N.Normal} :=
      ⟨⊥, inferInstance⟩
    calc
      fusionAxisEnvelopeTotal (preE7NonPairAction w U)
          (fun N =>
            ((toData P (by omega) hprimitive x D hgen hq horder hwindow).certificate
              .saprim).tailCoefficient b N) ≤
          fusionAxisEnvelopeTotal (preE7NonPairAction w U)
            (fun N => ((if N = B then
              (Nat.card (preE7NonPairAction w U ≃*
                preE7NonPairAction w U) : ℝ) else 0) + q)) := by
        unfold fusionAxisEnvelopeTotal
        apply Finset.sum_le_sum
        intro N _
        have hiff : N = B ↔ N.1 = ⊥ := ⟨
          fun hn => by simpa [B] using congrArg Subtype.val hn,
          fun hn => Subtype.ext (by simpa [B] using hn)⟩
        simpa only [hiff] using
          axis_tailCoefficient_le P (by omega) hprimitive x D hgen hq horder N
      _ = (Nat.card (preE7NonPairAction w U ≃*
              preE7NonPairAction w U) : ℝ) +
            (Nat.card {N : Subgroup (preE7NonPairAction w U) // N.Normal} : ℝ) * q := by
        unfold fusionAxisEnvelopeTotal
        rw [Finset.sum_add_distrib]
        simp [B, Finset.sum_const, nsmul_eq_mul]
        exact Or.inl (@Fintype.card_congr
          {N : Subgroup (preE7NonPairAction w U) // N.Normal}
          {N : Subgroup (preE7NonPairAction w U) // N.Normal}
          (Subtype.fintype Subgroup.Normal) originalNormalFintype (Equiv.refl _))
      _ ≤ _ := coefficient_menu P x hw hw1024 hqBound

noncomputable def toRankTailOwnerSource
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw : 27 ≤ w) (hw1024 : w < 1024)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (D : SolubleDerivedLength (P.complement x))
    (hgen : PermutationSubgroupGeneratorBound)
    {q : ℕ} (hq : 3 ≤ q) (horder : Nat.card (P.complement x) ≤ q)
    (hqBound : q ≤ 2 ^ ((Nat.log 2 w + 1) ^ 2))
    (hwindow : tailSlope q ≤ preE7CharacterWindow w) :
    PreE7RankTailOwnerSourceData w U :=
  .ordinary .saprim (.small
    (numericalData P hw hw1024 hprimitive x D hgen hq horder hqBound hwindow))

end PrimitiveAffineSolubleOddOrderSource

/-- Published solvable primitive-linear order bounds in the three degrees
not covered by the cyclic, binary, medium-dimension or general order rows. -/
structure PublishedSolublePrimitiveAffineExceptionalOrderInput where
  degreeTwentySeven : ∀ (U : PreE7NonPairActionClass 27)
    (P : PrimitiveAffineProfile (preE7NonPairAction 27 U) (Fin 27))
    (x : Fin 27), IsSolvable (P.complement x) →
      Nat.card (P.complement x) ≤ 78
  degreeFortyNine : ∀ (U : PreE7NonPairActionClass 49)
    (P : PrimitiveAffineProfile (preE7NonPairAction 49 U) (Fin 49))
    (x : Fin 49), IsSolvable (P.complement x) →
      Nat.card (P.complement x) ≤ 49 ^ 2
  degreeEightyOne : ∀ (U : PreE7NonPairActionClass 81)
    (P : PrimitiveAffineProfile (preE7NonPairAction 81 U) (Fin 81))
    (x : Fin 81), IsSolvable (P.complement x) →
      Nat.card (P.complement x) ≤ 81 ^ 3

namespace PrimitiveAffineSolubleOddExceptionalSource

private theorem window27 :
    PrimitiveAffineSolubleOddOrderSource.tailSlope 78 ≤
      preE7CharacterWindow 27 := by
  have hp : ((78 : ℝ) ^ 10) < (2 : ℝ) ^ (63 : ℕ) := by norm_num
  have hl := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by norm_num) 10) hp
  simp only [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hl
  unfold PrimitiveAffineSolubleOddOrderSource.tailSlope
    preE7CharacterWindow preE7CharacterRho halfDegree
  norm_num at hl ⊢
  linarith

private theorem window49 :
    PrimitiveAffineSolubleOddOrderSource.tailSlope (49 ^ 2) ≤
      preE7CharacterWindow 49 := by
  have hp : ((7 : ℝ) ^ (16 : ℕ)) < (2 : ℝ) ^ (45 : ℕ) := by norm_num
  have hl := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by norm_num) 16) hp
  simp only [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hl
  unfold PrimitiveAffineSolubleOddOrderSource.tailSlope
    preE7CharacterWindow preE7CharacterRho halfDegree
  have hq : (((49 ^ 2 : ℕ) : ℝ)) = (7 : ℝ) ^ (4 : ℕ) := by norm_num
  rw [hq, Real.logb_pow]
  norm_num at hl ⊢
  linarith

private theorem window81 :
    PrimitiveAffineSolubleOddOrderSource.tailSlope (81 ^ 3) ≤
      preE7CharacterWindow 81 := by
  have hp : ((3 : ℝ) ^ (5 : ℕ)) < (2 : ℝ) ^ (8 : ℕ) := by norm_num
  have hl := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by norm_num) 5) hp
  simp only [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hl
  unfold PrimitiveAffineSolubleOddOrderSource.tailSlope
    preE7CharacterWindow preE7CharacterRho halfDegree
  have hq : (((81 ^ 3 : ℕ) : ℝ)) = (3 : ℝ) ^ (12 : ℕ) := by norm_num
  rw [hq, Real.logb_pow]
  norm_num at hl ⊢
  linarith

private noncomputable def source27
    (published : PublishedSolublePrimitiveAffineExceptionalOrderInput)
    (hgen : PermutationSubgroupGeneratorBound)
    (U : PreE7NonPairActionClass 27)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 27 U) (Fin 27))
    (P : PrimitiveAffineProfile (preE7NonPairAction 27 U) (Fin 27))
    (hsolvable : IsSolvable (P.complement ⟨0, by norm_num⟩)) :
    PreE7RankTailOwnerSourceData 27 U := by
  let x : Fin 27 := ⟨0, by norm_num⟩
  by_cases hnontrivial : Nontrivial (P.complement x)
  · letI : Nontrivial (P.complement x) := hnontrivial
    letI : IsSolvable (P.complement x) := hsolvable
    let D : SolubleDerivedLength (P.complement x) :=
      Classical.choice (SolubleDerivedLength.nonempty _ inferInstance)
    apply PrimitiveAffineSolubleOddOrderSource.toRankTailOwnerSource
      P (by norm_num) (by norm_num) hprimitive x D hgen
      (q := 78) (by norm_num) (published.degreeTwentySeven U P x hsolvable)
    · norm_num [Nat.log]
    · exact window27
  · have hsub : Subsingleton (P.complement x) :=
      not_nontrivial_iff_subsingleton.mp hnontrivial
    letI : Subsingleton (P.complement x) := hsub
    let C : PrimitiveAffineDimensionOrderTailSource.CeilingData P := {
      m := 5
      width_lower := by norm_num
      order_le := by
        have hcomp : Nat.card (P.complement x) = 1 :=
          Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
        have hV : Nat.card P.V = 27 := by simpa using P.card_eq x
        rw [← (P.isComplement'_complement x).card_mul, hcomp, hV]
        norm_num
      slope_window := by
        norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree]
      menu_exponent := by norm_num }
    exact PrimitiveAffineDimensionOrderTailSource.toRankTailOwnerSource
      P C hprimitive x hgen

private noncomputable def source49
    (published : PublishedSolublePrimitiveAffineExceptionalOrderInput)
    (hgen : PermutationSubgroupGeneratorBound)
    (U : PreE7NonPairActionClass 49)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 49 U) (Fin 49))
    (P : PrimitiveAffineProfile (preE7NonPairAction 49 U) (Fin 49))
    (hsolvable : IsSolvable (P.complement ⟨0, by norm_num⟩)) :
    PreE7RankTailOwnerSourceData 49 U := by
  let x : Fin 49 := ⟨0, by norm_num⟩
  by_cases hnontrivial : Nontrivial (P.complement x)
  · letI : Nontrivial (P.complement x) := hnontrivial
    letI : IsSolvable (P.complement x) := hsolvable
    let D : SolubleDerivedLength (P.complement x) :=
      Classical.choice (SolubleDerivedLength.nonempty _ inferInstance)
    apply PrimitiveAffineSolubleOddOrderSource.toRankTailOwnerSource
      P (by norm_num) (by norm_num) hprimitive x D hgen
      (q := 49 ^ 2) (by norm_num) (published.degreeFortyNine U P x hsolvable)
    · norm_num [Nat.log]
    · exact window49
  · have hsub : Subsingleton (P.complement x) :=
      not_nontrivial_iff_subsingleton.mp hnontrivial
    letI : Subsingleton (P.complement x) := hsub
    let C : PrimitiveAffineDimensionOrderTailSource.CeilingData P := {
      m := 6
      width_lower := by norm_num
      order_le := by
        have hcomp : Nat.card (P.complement x) = 1 :=
          Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
        have hV : Nat.card P.V = 49 := by simpa using P.card_eq x
        rw [← (P.isComplement'_complement x).card_mul, hcomp, hV]
        norm_num
      slope_window := by
        norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree]
      menu_exponent := by norm_num }
    exact PrimitiveAffineDimensionOrderTailSource.toRankTailOwnerSource
      P C hprimitive x hgen

private noncomputable def source81
    (published : PublishedSolublePrimitiveAffineExceptionalOrderInput)
    (hgen : PermutationSubgroupGeneratorBound)
    (U : PreE7NonPairActionClass 81)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 81 U) (Fin 81))
    (P : PrimitiveAffineProfile (preE7NonPairAction 81 U) (Fin 81))
    (hsolvable : IsSolvable (P.complement ⟨0, by norm_num⟩)) :
    PreE7RankTailOwnerSourceData 81 U := by
  let x : Fin 81 := ⟨0, by norm_num⟩
  by_cases hnontrivial : Nontrivial (P.complement x)
  · letI : Nontrivial (P.complement x) := hnontrivial
    letI : IsSolvable (P.complement x) := hsolvable
    let D : SolubleDerivedLength (P.complement x) :=
      Classical.choice (SolubleDerivedLength.nonempty _ inferInstance)
    apply PrimitiveAffineSolubleOddOrderSource.toRankTailOwnerSource
      P (by norm_num) (by norm_num) hprimitive x D hgen
      (q := 81 ^ 3) (by norm_num) (published.degreeEightyOne U P x hsolvable)
    · norm_num [Nat.log]
    · exact window81
  · have hsub : Subsingleton (P.complement x) :=
      not_nontrivial_iff_subsingleton.mp hnontrivial
    letI : Subsingleton (P.complement x) := hsub
    let C : PrimitiveAffineDimensionOrderTailSource.CeilingData P := {
      m := 7
      width_lower := by norm_num
      order_le := by
        have hcomp : Nat.card (P.complement x) = 1 :=
          Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
        have hV : Nat.card P.V = 81 := by simpa using P.card_eq x
        rw [← (P.isComplement'_complement x).card_mul, hcomp, hV]
        norm_num
      slope_window := by
        norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree]
      menu_exponent := by norm_num }
    exact PrimitiveAffineDimensionOrderTailSource.toRankTailOwnerSource
      P C hprimitive x hgen

/-- The three exceptional soluble odd affine degrees as actual SAPRIM
owners. -/
noncomputable def rankTailOwnerSourceData
    {w : ℕ}
    (published : PublishedSolublePrimitiveAffineExceptionalOrderInput)
    (hgen : PermutationSubgroupGeneratorBound)
    (U : PreE7NonPairActionClass w)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hdegree : w = 27 ∨ w = 49 ∨ w = 81)
    (hsolvable : IsSolvable (P.complement ⟨0, by
      rcases hdegree with h | h | h <;> omega⟩)) :
    PreE7RankTailOwnerSourceData w U := by
  by_cases h27 : w = 27
  · subst w
    exact source27 published hgen U hprimitive P hsolvable
  by_cases h49 : w = 49
  · subst w
    exact source49 published hgen U hprimitive P hsolvable
  · have h81 : w = 81 := by
      rcases hdegree with h | h | h
      · exact False.elim (h27 h)
      · exact False.elim (h49 h)
      · exact h
    subst w
    exact source81 published hgen U hprimitive P hsolvable

end PrimitiveAffineSolubleOddExceptionalSource
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
