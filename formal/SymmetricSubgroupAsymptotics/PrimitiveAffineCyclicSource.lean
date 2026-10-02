import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileParity

/-!
# A profile-native cyclic-complement affine source

When the point stabilizer in a primitive affine profile is cyclic, every
nonbottom literal normal quotient is cyclic.  Those axes are paid by the
published Kovács--Praeger abelianization bound, while the bottom affine group
is paid by the internally proved derived cyclic-target theorem.  This gives a
pure additive row without identifying the action with a catalogue model.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineCyclicSource

variable {w : ℕ} {U : PreE7NonPairActionClass w}

private theorem bottom_epi_le
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw6 : 6 ≤ w)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (D : SolubleDerivedLength (P.complement x)) {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (preE7NonPairAction w U)) : ℝ) ≤
      (Nat.card (preE7NonPairAction w U ≃* preE7NonPairAction w U) : ℝ) *
        (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  letI : Nontrivial (Fin w) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h := (P.derivedCyclicTarget hprimitive x D).epi_card_le_prime J
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact mul_le_mul_of_nonneg_right
    (PrimitiveAffineSolubleSource.primitiveAffine_primeSlope_le_common P)
    (Nat.cast_nonneg b)

/-- Every literal normal axis of a cyclic-complement affine profile is paid
at the common odd-prime slope. -/
def axis
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw6 : 6 ≤ w)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (D : SolubleDerivedLength (P.complement x))
    (hcyclic : IsCyclic (P.complement x))
    (hKP : KovacsPraegerAbelianizationBound)
    (N : {N : Subgroup (preE7NonPairAction w U) // N.Normal}) :
    PreE7SmallAxisCertificate (preE7NonPairAction w U) N PUnit
      (Real.logb 2 3 / 3) := by
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
    exact bottom_epi_le P hw6 hprimitive x D J
  · refine .tail 1 zero_le_one ?_
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
    letI : IsCyclic (P.complement x) := hcyclic
    letI : IsCyclic (P.complement x ⧸ M) :=
      isCyclic_of_surjective (QuotientGroup.mk' M)
        (QuotientGroup.mk'_surjective M)
    rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e]
    calc
      (Nat.card (GroupEpimorphism J (P.complement x ⧸ M)) : ℝ) ≤
          Nat.card (Abelianization J) := by
        exact_mod_cast cyclicGroupEpimorphism_card_le_abelianization
          (J := J) (Q := P.complement x ⧸ M) inferInstance
      _ ≤ (3 : ℝ) ^ ((b : ℝ) / 3) := hKP b J
      _ = 1 * (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by
        rw [one_mul, three_rpow_third_eq]

private theorem axis_mainCoefficient
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw6 : 6 ≤ w)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (D : SolubleDerivedLength (P.complement x))
    (hcyclic : IsCyclic (P.complement x))
    (hKP : KovacsPraegerAbelianizationBound)
    (N : {N : Subgroup (preE7NonPairAction w U) // N.Normal}) :
    (axis P hw6 hprimitive x D hcyclic hKP N).mainCoefficient = 0 := by
  by_cases hN : N.1 = ⊥ <;>
    simp [axis, hN, PreE7SmallAxisCertificate.mainCoefficient]

private theorem axis_tailCoefficient_le
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw6 : 6 ≤ w)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (D : SolubleDerivedLength (P.complement x))
    (hcyclic : IsCyclic (P.complement x))
    (hKP : KovacsPraegerAbelianizationBound)
    (N : {N : Subgroup (preE7NonPairAction w U) // N.Normal}) :
    (axis P hw6 hprimitive x D hcyclic hKP N).tailCoefficient ≤
      1 + if N.1 = ⊥ then
        (Nat.card (preE7NonPairAction w U ≃* preE7NonPairAction w U) : ℝ)
      else 0 := by
  by_cases hN : N.1 = ⊥ <;>
    simp [axis, hN, PreE7SmallAxisCertificate.tailCoefficient]

/-- Pure-tail additive data for the cyclic-complement profile. -/
def toData
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw6 : 6 ≤ w)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (D : SolubleDerivedLength (P.complement x))
    (hcyclic : IsCyclic (P.complement x))
    (hKP : KovacsPraegerAbelianizationBound) :
    PreE7SmallAdditiveData w U where
  R := PUnit
  degree := 0
  action := 1
  action_injective := fun _ _ _ => Subsingleton.elim _ _
  tailSlope := Real.logb 2 3 / 3
  comparator_window := trivialSmallComparatorWindow hw6
  tail_window := logThreeThird_le_window hw6
  axis := axis P hw6 hprimitive x D hcyclic hKP

/-- Complete numerical data, with the axis and automorphism constants paid
by the uniform affine menu bound. -/
noncomputable def numericalData
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw6 : 6 ≤ w) (hw1024 : w < 1024)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (D : SolubleDerivedLength (P.complement x))
    (hcyclic : IsCyclic (P.complement x))
    (hKP : KovacsPraegerAbelianizationBound) :
    PreE7SmallAdditiveNumericalData .saprim w U where
  data := toData P hw6 hprimitive x D hcyclic hKP
  main_total_bound := by
    intro b
    have hz :
        fusionAxisEnvelopeTotal (preE7NonPairAction w U)
          (fun N => ((toData P hw6 hprimitive x D hcyclic hKP).certificate
            .saprim).C b N) = 0 := by
      unfold fusionAxisEnvelopeTotal
      apply Finset.sum_eq_zero
      intro N _
      exact axis_mainCoefficient P hw6 hprimitive x D hcyclic hKP N
    rw [hz]
    exact Real.rpow_nonneg (by norm_num) _
  tail_total_bound := by
    intro b
    let B : {N : Subgroup (preE7NonPairAction w U) // N.Normal} := ⟨⊥, inferInstance⟩
    calc
      fusionAxisEnvelopeTotal (preE7NonPairAction w U)
          (fun N => ((toData P hw6 hprimitive x D hcyclic hKP).certificate
            .saprim).tailCoefficient b N) ≤
          fusionAxisEnvelopeTotal (preE7NonPairAction w U)
            (fun N => (1 : ℝ) + if N = B then
              (Nat.card (preE7NonPairAction w U ≃* preE7NonPairAction w U) : ℝ)
            else 0) := by
        unfold fusionAxisEnvelopeTotal
        apply Finset.sum_le_sum
        intro N _
        have h := axis_tailCoefficient_le P hw6 hprimitive x D hcyclic hKP N
        convert h using 1
        congr 2
        exact propext ⟨
          fun hn => by simpa [B] using congrArg Subtype.val hn,
          fun hn => Subtype.ext (by simpa [B] using hn)⟩
      _ = (Nat.card {N : Subgroup (preE7NonPairAction w U) // N.Normal} : ℝ) +
          Nat.card (preE7NonPairAction w U ≃* preE7NonPairAction w U) := by
        unfold fusionAxisEnvelopeTotal
        rw [Finset.sum_add_distrib]
        simp [B]
        exact @Fintype.card_congr
          {N : Subgroup (preE7NonPairAction w U) // N.Normal}
          {N : Subgroup (preE7NonPairAction w U) // N.Normal}
          (Subtype.fintype Subgroup.Normal) originalNormalFintype (Equiv.refl _)
      _ ≤ _ := by
        apply primitiveAffine_small_menu_bound (by omega) hw1024
        exact P.card_le_two_pow_logSquare x

/-- Concrete SAPRIM owner source for a cyclic-complement affine profile. -/
noncomputable def toRankTailOwnerSource
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw6 : 6 ≤ w) (hw1024 : w < 1024)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (D : SolubleDerivedLength (P.complement x))
    (hcyclic : IsCyclic (P.complement x))
    (hKP : KovacsPraegerAbelianizationBound) :
    PreE7RankTailOwnerSourceData w U :=
  .ordinary .saprim (.small
    (numericalData P hw6 hw1024 hprimitive x D hcyclic hKP))

end PrimitiveAffineCyclicSource
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
