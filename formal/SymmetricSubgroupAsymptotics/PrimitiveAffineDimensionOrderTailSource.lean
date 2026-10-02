import SymmetricSubgroupAsymptotics.PrimitiveAffineDimensionOrder
import SymmetricSubgroupAsymptotics.PrimitiveAffineOrderTailSource

/-!
# Dimension-sensitive affine order-tail owners

This is the parameterized form of the medium affine order-tail argument.
Instead of fixing the coarse exponent `(log₂ w + 1)^2`, it accepts any
proved binary order ceiling `|L| ≤ 2^m`.  The only numerical obligations are
the exact tail window and the finite menu-mass inequality.  The preceding
dimension theorem supplies such ceilings intrinsically from the translation
dimension.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineDimensionOrderTailSource

variable {w : ℕ} {U : PreE7NonPairActionClass w}

/-- A sharp binary order ceiling for one literal primitive affine profile,
together with exactly the two numerical checks needed by the recurrence. -/
structure CeilingData
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w)) where
  m : ℕ
  width_lower : 8 ≤ w
  order_le : Nat.card (preE7NonPairAction w U) ≤ 2 ^ m
  slope_window : (m : ℝ) / 2 ≤ preE7CharacterWindow w
  menu_exponent : m * m + m + 1 ≤ 64 * w

def tailSlope
    {P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w)}
    (D : CeilingData P) : ℝ := D.m / 2

/-- Every normal axis is a pure tail.  The bottom uses the whole affine
order ceiling; every nonbottom axis is a quotient of the point stabilizer
and hence obeys the same ceiling. -/
def axis
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (D : CeilingData P)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w)
    (hgen : PermutationSubgroupGeneratorBound)
    (N : {N : Subgroup (preE7NonPairAction w U) // N.Normal}) :
    PreE7SmallAxisCertificate (preE7NonPairAction w U) N PUnit
      (tailSlope D) := by
  have hw := D.width_lower
  letI : Nontrivial (Fin w) := Fin.nontrivial_iff_two_le.mpr (by omega)
  haveI : N.1.Normal := N.2
  by_cases hN : N.1 = ⊥
  · refine .tail ((2 : ℝ) ^ D.m) (by positivity) ?_
    intro b J
    let e : (preE7NonPairAction w U ⧸ N.1) ≃*
        preE7NonPairAction w U :=
      (QuotientGroup.quotientMulEquivOfEq hN).trans QuotientGroup.quotientBot
    rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e]
    simpa [tailSlope] using
      (PrimitiveAffineOrderTailSource.epi_le_twoPowerCeiling
        hgen J D.order_le)
  · refine .tail ((2 : ℝ) ^ D.m) (by positivity) ?_
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
    apply PrimitiveAffineOrderTailSource.epi_le_twoPowerCeiling hgen J
    calc
      Nat.card (P.complement x ⧸ M) ≤ Nat.card (P.complement x) :=
        Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective (s := M))
      _ ≤ Nat.card (preE7NonPairAction w U) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ ≤ 2 ^ D.m := D.order_le

private theorem axis_mainCoefficient
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (D : CeilingData P)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w)
    (hgen : PermutationSubgroupGeneratorBound)
    (N : {N : Subgroup (preE7NonPairAction w U) // N.Normal}) :
    (axis P D hprimitive x hgen N).mainCoefficient = 0 := by
  by_cases hN : N.1 = ⊥ <;>
    simp [axis, hN, PreE7SmallAxisCertificate.mainCoefficient]

private theorem axis_tailCoefficient_le
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (D : CeilingData P)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w)
    (hgen : PermutationSubgroupGeneratorBound)
    (N : {N : Subgroup (preE7NonPairAction w U) // N.Normal}) :
    (axis P D hprimitive x hgen N).tailCoefficient ≤ (2 : ℝ) ^ D.m := by
  by_cases hN : N.1 = ⊥ <;>
    simp [axis, hN, PreE7SmallAxisCertificate.tailCoefficient]

def toData
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (D : CeilingData P)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w)
    (hgen : PermutationSubgroupGeneratorBound) :
    PreE7SmallAdditiveData w U where
  R := PUnit
  degree := 0
  action := 1
  action_injective := fun _ _ _ => Subsingleton.elim _ _
  tailSlope := tailSlope D
  comparator_window := trivialSmallComparatorWindow (by
    have hw := D.width_lower
    omega)
  tail_window := D.slope_window
  axis := axis P D hprimitive x hgen

private theorem coefficient_menu
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (D : CeilingData P) (b : ℕ) :
    (Nat.card {N : Subgroup (preE7NonPairAction w U) // N.Normal} : ℝ) *
          (2 : ℝ) ^ D.m ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  have hnormal :
      Nat.card {N : Subgroup (preE7NonPairAction w U) // N.Normal} ≤
        2 ^ (D.m * D.m) :=
    normalSubgroup_card_le_two_pow_sq D.m D.order_le
  have hnat :
      Nat.card {N : Subgroup (preE7NonPairAction w U) // N.Normal} * 2 ^ D.m ≤
        2 ^ (D.m * D.m + D.m + 1) := by
    calc
      _ ≤ 2 ^ (D.m * D.m) * 2 ^ D.m := Nat.mul_le_mul_right _ hnormal
      _ = 2 ^ (D.m * D.m + D.m) := by rw [pow_add]
      _ ≤ 2 ^ (D.m * D.m + D.m + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
  calc
    _ ≤ ((2 ^ (D.m * D.m + D.m + 1) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    _ = (2 : ℝ) ^ ((D.m * D.m + D.m + 1 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      norm_num
    _ ≤ (2 : ℝ) ^ (64 * (w : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact_mod_cast D.menu_exponent
    _ ≤ _ := two_rpow_sixtyFour_width_le_menuMass D.width_lower b

noncomputable def numericalData
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (D : CeilingData P)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w)
    (hgen : PermutationSubgroupGeneratorBound) :
    PreE7SmallAdditiveNumericalData .saprim w U where
  data := toData P D hprimitive x hgen
  main_total_bound := by
    intro b
    have hz : fusionAxisEnvelopeTotal (preE7NonPairAction w U)
        (fun N => ((toData P D hprimitive x hgen).certificate
          .saprim).C b N) = 0 := by
      unfold fusionAxisEnvelopeTotal
      apply Finset.sum_eq_zero
      intro N _
      exact axis_mainCoefficient P D hprimitive x hgen N
    rw [hz]
    exact Real.rpow_nonneg (by norm_num) _
  tail_total_bound := by
    intro b
    calc
      fusionAxisEnvelopeTotal (preE7NonPairAction w U)
          (fun N => ((toData P D hprimitive x hgen).certificate
            .saprim).tailCoefficient b N) ≤
          fusionAxisEnvelopeTotal (preE7NonPairAction w U)
            (fun _N => (2 : ℝ) ^ D.m) := by
        unfold fusionAxisEnvelopeTotal
        apply Finset.sum_le_sum
        intro N _
        exact axis_tailCoefficient_le P D hprimitive x hgen N
      _ = (Nat.card {N : Subgroup (preE7NonPairAction w U) // N.Normal} : ℝ) *
            (2 : ℝ) ^ D.m := by
        unfold fusionAxisEnvelopeTotal
        simp [Finset.sum_const, nsmul_eq_mul]
        exact @Fintype.card_congr
          {N : Subgroup (preE7NonPairAction w U) // N.Normal}
          {N : Subgroup (preE7NonPairAction w U) // N.Normal}
          (Subtype.fintype Subgroup.Normal) originalNormalFintype (Equiv.refl _)
      _ ≤ _ := coefficient_menu P D b

noncomputable def toRankTailOwnerSource
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (D : CeilingData P)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w)
    (hgen : PermutationSubgroupGeneratorBound) :
    PreE7RankTailOwnerSourceData w U :=
  .ordinary .saprim (.small (numericalData P D hprimitive x hgen))

/-- The intrinsic vector-space dimension theorem constructs the binary
ceiling required above from one elementary chart. -/
noncomputable def ceilingDataOfDimension
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    [Nontrivial (Fin w)]
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (m : ℕ)
    (hwidth : 8 ≤ w)
    (hpow : w ^ ((P.elementaryChart hprimitive).d + 1) ≤ 2 ^ m)
    (hslope : (m : ℝ) / 2 ≤ preE7CharacterWindow w)
    (hmenu : m * m + m + 1 ≤ 64 * w) : CeilingData P where
  m := m
  width_lower := hwidth
  order_le := by
    let C := P.elementaryChart hprimitive
    letI : Finite C.V := Finite.of_injective
      (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
      C.equiv.symm.injective
    exact (P.card_le_degree_pow_finrank_succ C.equiv x).trans (by
      simpa [C, PrimitiveAffineProfile.ElementaryChart.d] using hpow)
  slope_window := hslope
  menu_exponent := hmenu

end PrimitiveAffineDimensionOrderTailSource
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
