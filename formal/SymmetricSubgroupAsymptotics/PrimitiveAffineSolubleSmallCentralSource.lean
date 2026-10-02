import SymmetricSubgroupAsymptotics.DegreeNineCentralProductComparator
import SymmetricSubgroupAsymptotics.DegreeTwentyFiveCentralFourBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeNineCentralProductModel
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeNineSolvable
import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileParity
import SymmetricSubgroupAsymptotics.PrimitiveAffineNormalAxisReduction
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelNumerics

/-!
# The two small soluble odd affine owners from structural catalogue data

The degree-nine and degree-twenty-five counting inequalities are theorems in
`DegreeNineCentralProductComparator` and
`DegreeTwentyFiveCentralFourBound`.  The only external input retained here
is the published finite subgroup structure of soluble subgroups of
`GL₂(3)` and `GL₂(5)`: complement-order ceilings and the literal central
quotient models.  This file proves the affine bottom fibre, all nonbottom
normal-axis reductions, coefficient totals, and the final SAPRIM owners.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Published finite structural information for the remaining exceptional
small soluble primitive-linear group.  The degree-nine model is now proved
from the literal affine representation and is no longer an input. -/
structure PublishedSolublePrimitiveAffineSmallCentralInput where
  degreeTwentyFiveModel : ∀ (U : PreE7NonPairActionClass 25)
    (P : PrimitiveAffineProfile (preE7NonPairAction 25 U) (Fin 25))
    (_hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 25 U) (Fin 25))
    (x : Fin 25), IsSolvable (P.complement x) →
      DegreeTwentyFiveCentralFourModel (P.complement x)

private theorem automorphism_card_le_two_pow_sq
    {G : Type*} [Group G] [Finite G] (m : ℕ)
    (horder : Nat.card G ≤ 2 ^ m) :
    Nat.card (G ≃* G) ≤ 2 ^ (m * m) := by
  calc
    Nat.card (G ≃* G) ≤ Nat.card G ^ Nat.log 2 (Nat.card G) :=
      mulEquiv_card_le_card_pow_log G
    _ ≤ (2 ^ m) ^ Nat.log 2 (Nat.card G) :=
      Nat.pow_le_pow_left horder _
    _ ≤ (2 ^ m) ^ m := by
      apply Nat.pow_le_pow_right (by positivity)
      exact (Nat.log_mono_right (b := 2) horder).trans_eq
        (Nat.log_pow (by norm_num) m)
    _ = 2 ^ (m * m) := by rw [pow_mul]

private theorem nat_two_pow_le_menu
    {w e b : ℕ} (hw : 8 ≤ w) (he : e ≤ 64 * w) :
    ((2 ^ e : ℕ) : ℝ) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  calc
    ((2 ^ e : ℕ) : ℝ) = (2 : ℝ) ^ (e : ℝ) := by
      rw [Real.rpow_natCast]
      norm_num
    _ ≤ (2 : ℝ) ^ (64 * (w : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact_mod_cast he
    _ ≤ _ := two_rpow_sixtyFour_width_le_menuMass hw b

private theorem affine_order_le_of_complement
    {w m q : ℕ} {U : PreE7NonPairActionClass w}
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (hcomp : Nat.card (P.complement x) ≤ q)
    (hproduct : w * q ≤ 2 ^ m) :
    Nat.card (preE7NonPairAction w U) ≤ 2 ^ m := by
  have hV : Nat.card P.V = w := by simpa using P.card_eq x
  calc
    Nat.card (preE7NonPairAction w U) =
        Nat.card P.V * Nat.card (P.complement x) :=
      (P.isComplement'_complement x).card_mul.symm
    _ ≤ w * q := by rw [hV]; exact Nat.mul_le_mul_left _ hcomp
    _ ≤ 2 ^ m := hproduct

private theorem affine_bottom_epi_le
    {w : ℕ} {U : PreE7NonPairActionClass w}
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw : 6 ≤ w)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (D : SolubleDerivedLength (P.complement x))
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (preE7NonPairAction w U)) : ℝ) ≤
      (Nat.card (preE7NonPairAction w U ≃*
        preE7NonPairAction w U) : ℝ) *
        (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  letI : Nontrivial (Fin w) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h := (P.derivedCyclicTarget hprimitive x D).epi_card_le_prime J
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact mul_le_mul_of_nonneg_right
    (PrimitiveAffineSolubleSource.primitiveAffine_primeSlope_le_common P)
    (Nat.cast_nonneg b)

/-! ## Degree nine -/

namespace PrimitiveAffineDegreeNineCentralSource

variable (U : PreE7NonPairActionClass 9)
  (P : PrimitiveAffineProfile (preE7NonPairAction 9 U) (Fin 9))
  (hprimitive : MulAction.IsPreprimitive
    (preE7NonPairAction 9 U) (Fin 9))
  (x : Fin 9) (D : SolubleDerivedLength (P.complement x))
  (hcomp : Nat.card (P.complement x) ≤ 48)
  (M : DegreeNineCentralProductModel (P.complement x))

private abbrev Axis :=
  {N : Subgroup (preE7NonPairAction 9 U) // N.Normal}

def axis (N : Axis U) :
    PreE7SmallAxisCertificate (preE7NonPairAction 9 U) N M.Q
      (Real.logb 2 3 / 3) := by
  by_cases hN : N.1 = ⊥
  · refine .tail
      (Nat.card (preE7NonPairAction 9 U ≃* preE7NonPairAction 9 U))
      (Nat.cast_nonneg _) ?_
    intro b J
    let e : (preE7NonPairAction 9 U ⧸ N.1) ≃*
        preE7NonPairAction 9 U :=
      (QuotientGroup.quotientMulEquivOfEq hN).trans
        QuotientGroup.quotientBot
    rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e]
    exact affine_bottom_epi_le P (by norm_num) hprimitive x D J
  · refine .bounded M.coefficient 0 (Nat.cast_nonneg _) le_rfl ?_
    intro b J _
    calc
      (Nat.card (GroupEpimorphism J
          (preE7NonPairAction 9 U ⧸ N.1)) : ℝ) ≤
          completeQuotientWeight (R := P.complement x) J :=
        P.nonbottom_epimorphism_card_le_completeComplementWeight
          hprimitive x J N hN
      _ ≤ (M.coefficient : ℝ) *
          completeQuotientWeight (R := M.Q) J := by
        simpa [DegreeNineCentralProductModel.toComparator] using
          M.toComparator.complete_bound J
      _ = (M.coefficient : ℝ) * completeQuotientWeight (R := M.Q) J +
          0 * (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by
        ring

private theorem axis_main_le (N : Axis U) :
    (axis U P hprimitive x D M N).mainCoefficient ≤ M.coefficient := by
  by_cases hN : N.1 = ⊥ <;>
    simp [axis, hN, PreE7SmallAxisCertificate.mainCoefficient]

private theorem axis_tail_le (N : Axis U) :
    (axis U P hprimitive x D M N).tailCoefficient ≤
      if N.1 = ⊥ then
        (Nat.card (preE7NonPairAction 9 U ≃*
          preE7NonPairAction 9 U) : ℝ) else 0 := by
  by_cases hN : N.1 = ⊥ <;>
    simp [axis, hN, PreE7SmallAxisCertificate.tailCoefficient]

def toData : PreE7SmallAdditiveData 9 U where
  R := M.Q
  degree := 6
  action := M.Q.subtype
  action_injective := Subtype.val_injective
  tailSlope := Real.logb 2 3 / 3
  comparator_window := by
    norm_num [preE7CharacterRho, evenWidth, halfDegree]
  tail_window := logThreeThird_le_window (by norm_num)
  axis := axis U P hprimitive x D M

include P x hcomp in
private theorem action_order :
    Nat.card (preE7NonPairAction 9 U) ≤ 2 ^ 9 :=
  affine_order_le_of_complement P x hcomp (by norm_num)

include P x hcomp M in
private theorem main_menu (b : ℕ) :
    (Nat.card (Axis U) : ℝ) * M.coefficient ≤
      (2 : ℝ) ^
        (16 * (9 : ℝ) * Real.log ((9 + b + 2 : ℕ) : ℝ) ^ 2) := by
  have hnormal : Nat.card (Axis U) ≤ 2 ^ 81 := by
    simpa using normalSubgroup_card_le_two_pow_sq 9
      (action_order U P x hcomp)
  have hcoeff : M.coefficient ≤ 2 ^ 72 := M.coefficient_le hcomp
  have hnat : Nat.card (Axis U) * M.coefficient ≤ 2 ^ 153 := by
    calc
      _ ≤ 2 ^ 81 * 2 ^ 72 := Nat.mul_le_mul hnormal hcoeff
      _ = 2 ^ 153 := by rw [← pow_add]
  calc
    _ ≤ ((2 ^ 153 : ℕ) : ℝ) := by exact_mod_cast hnat
    _ ≤ _ := nat_two_pow_le_menu (w := 9) (b := b) (by norm_num) (by norm_num)

include P x hcomp in
private theorem tail_menu (b : ℕ) :
    (Nat.card (preE7NonPairAction 9 U ≃*
      preE7NonPairAction 9 U) : ℝ) ≤
      (2 : ℝ) ^
        (16 * (9 : ℝ) * Real.log ((9 + b + 2 : ℕ) : ℝ) ^ 2) := by
  have haut := automorphism_card_le_two_pow_sq 9
    (action_order U P x hcomp)
  calc
    _ ≤ ((2 ^ 81 : ℕ) : ℝ) := by exact_mod_cast haut
    _ ≤ _ := nat_two_pow_le_menu (w := 9) (b := b) (by norm_num) (by norm_num)

include P hprimitive x D hcomp M in
noncomputable def numericalData :
    PreE7SmallAdditiveNumericalData .saprim 9 U where
  data := toData U P hprimitive x D M
  main_total_bound := by
    intro b
    calc
      fusionAxisEnvelopeTotal (preE7NonPairAction 9 U)
          (fun N => ((toData U P hprimitive x D M).certificate
            .saprim).C b N) ≤
          fusionAxisEnvelopeTotal (preE7NonPairAction 9 U)
            (fun _N => (M.coefficient : ℝ)) := by
        unfold fusionAxisEnvelopeTotal
        apply Finset.sum_le_sum
        intro N _
        exact axis_main_le U P hprimitive x D M N
      _ = (Nat.card (Axis U) : ℝ) * M.coefficient := by
        unfold fusionAxisEnvelopeTotal
        simp [Finset.sum_const, nsmul_eq_mul]
        exact Or.inl (@Fintype.card_congr (Axis U) (Axis U)
          (Subtype.fintype Subgroup.Normal) originalNormalFintype (Equiv.refl _))
      _ ≤ _ := main_menu U P x hcomp M b
  tail_total_bound := by
    intro b
    let B : Axis U := ⟨⊥, inferInstance⟩
    calc
      fusionAxisEnvelopeTotal (preE7NonPairAction 9 U)
          (fun N => ((toData U P hprimitive x D M).certificate
            .saprim).tailCoefficient b N) ≤
          fusionAxisEnvelopeTotal (preE7NonPairAction 9 U)
            (fun N => if N = B then
              (Nat.card (preE7NonPairAction 9 U ≃*
                preE7NonPairAction 9 U) : ℝ) else 0) := by
        unfold fusionAxisEnvelopeTotal
        apply Finset.sum_le_sum
        intro N _
        have hiff : N = B ↔ N.1 = ⊥ := ⟨
          fun hn => by simpa [B] using congrArg Subtype.val hn,
          fun hn => Subtype.ext (by simpa [B] using hn)⟩
        simpa only [hiff] using axis_tail_le U P hprimitive x D M N
      _ = (Nat.card (preE7NonPairAction 9 U ≃*
          preE7NonPairAction 9 U) : ℝ) := by
        unfold fusionAxisEnvelopeTotal
        simp [B]
      _ ≤ _ := tail_menu U P x hcomp b

include P hprimitive x D hcomp M in
noncomputable def toRankTailOwnerSource :
    PreE7RankTailOwnerSourceData 9 U :=
  .ordinary .saprim (.small
    (numericalData U P hprimitive x D hcomp M))

end PrimitiveAffineDegreeNineCentralSource

/-! ## Degree twenty-five -/

namespace PrimitiveAffineDegreeTwentyFiveCentralSource

variable (U : PreE7NonPairActionClass 25)
  (P : PrimitiveAffineProfile (preE7NonPairAction 25 U) (Fin 25))
  (hprimitive : MulAction.IsPreprimitive
    (preE7NonPairAction 25 U) (Fin 25))
  (x : Fin 25) (D : SolubleDerivedLength (P.complement x))
  (hcomp : Nat.card (P.complement x) ≤ 96)
  (M : DegreeTwentyFiveCentralFourModel (P.complement x))
  (hgen : PermutationSubgroupGeneratorBound)
  (hKP : KovacsPraegerAbelianizationBound)

private abbrev Axis :=
  {N : Subgroup (preE7NonPairAction 25 U) // N.Normal}

def axis (N : Axis U) :
    PreE7SmallAxisCertificate (preE7NonPairAction 25 U) N PUnit
      degreeTwentyFiveCentralSlope := by
  by_cases hN : N.1 = ⊥
  · refine .tail
      (Nat.card (preE7NonPairAction 25 U ≃* preE7NonPairAction 25 U))
      (Nat.cast_nonneg _) ?_
    intro b J
    let e : (preE7NonPairAction 25 U ⧸ N.1) ≃*
        preE7NonPairAction 25 U :=
      (QuotientGroup.quotientMulEquivOfEq hN).trans
        QuotientGroup.quotientBot
    rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e]
    have hbottom := affine_bottom_epi_le P (by norm_num) hprimitive x D J
    refine hbottom.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg b)
    unfold degreeTwentyFiveCentralSlope
    have hlog : 0 ≤ Real.logb 2 24 :=
      Real.logb_nonneg (by norm_num) (by norm_num)
    linarith
  · refine .tail M.coefficient M.coefficient_nonneg ?_
    intro b J
    exact (P.nonbottom_epimorphism_card_le_completeComplementWeight
      hprimitive x J N hN).trans (M.complete_bound hgen hKP J)

private theorem axis_main_zero (N : Axis U) :
    (axis U P hprimitive x D M hgen hKP N).mainCoefficient = 0 := by
  by_cases hN : N.1 = ⊥ <;>
    simp [axis, hN, PreE7SmallAxisCertificate.mainCoefficient]

private theorem axis_tail_le (N : Axis U) :
    (axis U P hprimitive x D M hgen hKP N).tailCoefficient ≤
      (if N.1 = ⊥ then
        (Nat.card (preE7NonPairAction 25 U ≃*
          preE7NonPairAction 25 U) : ℝ) else 0) + M.coefficient := by
  by_cases hN : N.1 = ⊥ <;>
    simp [axis, hN, PreE7SmallAxisCertificate.tailCoefficient,
      M.coefficient_nonneg]

def toData : PreE7SmallAdditiveData 25 U where
  R := PUnit
  degree := 0
  action := 1
  action_injective := fun _ _ _ => Subsingleton.elim _ _
  tailSlope := degreeTwentyFiveCentralSlope
  comparator_window := trivialSmallComparatorWindow (by norm_num)
  tail_window := by
    have hp24 : (24 : ℝ) ^ 5 < (2 : ℝ) ^ (23 : ℕ) := by norm_num
    have h24 := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
      (pow_pos (by norm_num) 5) hp24
    simp only [Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at h24
    have hp3 : (3 : ℝ) ^ 5 < (2 : ℝ) ^ (8 : ℕ) := by norm_num
    have h3 := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
      (pow_pos (by norm_num) 5) hp3
    simp only [Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at h3
    unfold degreeTwentyFiveCentralSlope preE7CharacterWindow
      preE7CharacterRho halfDegree
    norm_num at h24 h3 ⊢
    linarith
  axis := axis U P hprimitive x D M hgen hKP

include P x hcomp in
private theorem action_order :
    Nat.card (preE7NonPairAction 25 U) ≤ 2 ^ 12 :=
  affine_order_le_of_complement P x hcomp (by norm_num)

include P x hcomp M in
private theorem tail_menu (b : ℕ) :
    (Nat.card (preE7NonPairAction 25 U ≃*
        preE7NonPairAction 25 U) : ℝ) +
      (Nat.card (Axis U) : ℝ) * M.coefficient ≤
        (2 : ℝ) ^
          (16 * (25 : ℝ) * Real.log ((25 + b + 2 : ℕ) : ℝ) ^ 2) := by
  have hnormal : Nat.card (Axis U) ≤ 2 ^ 144 := by
    simpa using normalSubgroup_card_le_two_pow_sq 12
      (action_order U P x hcomp)
  have haut : Nat.card (preE7NonPairAction 25 U ≃*
      preE7NonPairAction 25 U) ≤ 2 ^ 144 :=
    automorphism_card_le_two_pow_sq 12 (action_order U P x hcomp)
  have hcoeff : M.coefficient ≤ (2 : ℝ) ^ (54 : ℕ) := by
    simpa using M.coefficient_le hcomp
  have hnormalR : (Nat.card (Axis U) : ℝ) ≤ (2 : ℝ) ^ (144 : ℕ) := by
    exact_mod_cast hnormal
  have hautR : (Nat.card (preE7NonPairAction 25 U ≃*
      preE7NonPairAction 25 U) : ℝ) ≤ (2 : ℝ) ^ (144 : ℕ) := by
    exact_mod_cast haut
  calc
    _ ≤ (2 : ℝ) ^ (144 : ℕ) +
        (2 : ℝ) ^ (144 : ℕ) * (2 : ℝ) ^ (54 : ℕ) :=
      add_le_add hautR
        (mul_le_mul hnormalR hcoeff M.coefficient_nonneg (by positivity))
    _ ≤ (2 : ℝ) ^ (198 : ℕ) + (2 : ℝ) ^ (198 : ℕ) := by
      rw [← pow_add]
      exact add_le_add
        (pow_le_pow_right₀ (by norm_num) (by norm_num)) le_rfl
    _ = ((2 ^ 199 : ℕ) : ℝ) := by norm_num [pow_succ]
    _ ≤ _ := nat_two_pow_le_menu (w := 25) (b := b)
      (by norm_num) (by norm_num)

include P hprimitive x D hcomp M hgen hKP in
noncomputable def numericalData :
    PreE7SmallAdditiveNumericalData .saprim 25 U where
  data := toData U P hprimitive x D M hgen hKP
  main_total_bound := by
    intro b
    have hz : fusionAxisEnvelopeTotal (preE7NonPairAction 25 U)
        (fun N => ((toData U P hprimitive x D M hgen hKP).certificate
          .saprim).C b N) = 0 := by
      unfold fusionAxisEnvelopeTotal
      apply Finset.sum_eq_zero
      intro N _
      exact axis_main_zero U P hprimitive x D M hgen hKP N
    rw [hz]
    exact Real.rpow_nonneg (by norm_num) _
  tail_total_bound := by
    intro b
    let B : Axis U := ⟨⊥, inferInstance⟩
    calc
      fusionAxisEnvelopeTotal (preE7NonPairAction 25 U)
          (fun N => ((toData U P hprimitive x D M hgen hKP).certificate
            .saprim).tailCoefficient b N) ≤
          fusionAxisEnvelopeTotal (preE7NonPairAction 25 U)
            (fun N => ((if N = B then
              (Nat.card (preE7NonPairAction 25 U ≃*
                preE7NonPairAction 25 U) : ℝ) else 0) + M.coefficient)) := by
        unfold fusionAxisEnvelopeTotal
        apply Finset.sum_le_sum
        intro N _
        have hiff : N = B ↔ N.1 = ⊥ := ⟨
          fun hn => by simpa [B] using congrArg Subtype.val hn,
          fun hn => Subtype.ext (by simpa [B] using hn)⟩
        simpa only [hiff] using
          axis_tail_le U P hprimitive x D M hgen hKP N
      _ = (Nat.card (preE7NonPairAction 25 U ≃*
              preE7NonPairAction 25 U) : ℝ) +
            (Nat.card (Axis U) : ℝ) * M.coefficient := by
        unfold fusionAxisEnvelopeTotal
        rw [Finset.sum_add_distrib]
        simp [B, Finset.sum_const, nsmul_eq_mul]
        exact Or.inl (@Fintype.card_congr (Axis U) (Axis U)
          (Subtype.fintype Subgroup.Normal) originalNormalFintype (Equiv.refl _))
      _ ≤ _ := tail_menu U P x hcomp M b

include P hprimitive x D hcomp M hgen hKP in
noncomputable def toRankTailOwnerSource :
    PreE7RankTailOwnerSourceData 25 U :=
  .ordinary .saprim (.small
    (numericalData U P hprimitive x D hcomp M hgen hKP))

end PrimitiveAffineDegreeTwentyFiveCentralSource

/-! ## Published structural data to owners -/

noncomputable def primitiveAffineSolubleSmallCentral_rankTailOwnerSourceData
    {w : ℕ}
    (published : PublishedSolublePrimitiveAffineSmallCentralInput)
    (hgen : PermutationSubgroupGeneratorBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (U : PreE7NonPairActionClass w)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hdegree : w = 9 ∨ w = 25)
    (hsolvable : IsSolvable (P.complement ⟨0, by omega⟩)) :
    PreE7RankTailOwnerSourceData w U := by
  by_cases h9 : w = 9
  · subst w
    let x : Fin 9 := ⟨0, by norm_num⟩
    letI : Nontrivial (P.complement x) :=
      complement_nontrivial_of_proper_prime_divisor P hprimitive x
        (q := 3) (by norm_num) (by norm_num) (by norm_num)
    letI : IsSolvable (P.complement x) := hsolvable
    let D : SolubleDerivedLength (P.complement x) :=
      Classical.choice (SolubleDerivedLength.nonempty _ inferInstance)
    exact PrimitiveAffineDegreeNineCentralSource.toRankTailOwnerSource
      U P hprimitive x D (P.complement_card_le_48_degreeNine hprimitive x)
      (P.degreeNineCentralProductModel hprimitive x)
  · have h25 : w = 25 := hdegree.resolve_left h9
    subst w
    let x : Fin 25 := ⟨0, by norm_num⟩
    letI : Nontrivial (P.complement x) :=
      complement_nontrivial_of_proper_prime_divisor P hprimitive x
        (q := 5) (by norm_num) (by norm_num) (by norm_num)
    letI : IsSolvable (P.complement x) := hsolvable
    let D : SolubleDerivedLength (P.complement x) :=
      Classical.choice (SolubleDerivedLength.nonempty _ inferInstance)
    let M := published.degreeTwentyFiveModel U P hprimitive x hsolvable
    exact PrimitiveAffineDegreeTwentyFiveCentralSource.toRankTailOwnerSource
      U P hprimitive x D M.source_card_le_96 M hgen hKP

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
