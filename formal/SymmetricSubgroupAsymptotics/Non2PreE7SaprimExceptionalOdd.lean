import SymmetricSubgroupAsymptotics.Non2PreE7SaprimOddLargeAffine

/-!
# Exceptional odd primitive affine SAPRIM rows

The finite soluble-affine theorem has two exceptional odd degrees which are
not consequences of a cyclic complement or a plain complement-order bound.

* At degree nine, the scalar kernel of `R ≤ GL₂(3)` has order at most two.
  The audited central-product theorem compares the complete quotient weight
  of `R` with that of the faithful six-point comparator `P × C₂`.
* At degree twenty-five, every literal complement quotient is a central
  cyclic extension of a soluble projective group of order at most 24.  The
  audited central-`C₄` theorem bounds the complete quotient weight at slope
  `log₂(48)/2`.

The two named input structures below are precisely those published finite
group statements.  This file proves everything after them: the affine bottom
fibre, transport of every literal normal axis, the strict numerical windows,
and both finite coefficient sums required by the T1 owner package.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

open AffineModel Equiv SemidirectProduct

local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

private abbrev NormalAxis {w : ℕ} (i : PreE7NonPairActionClass w) :=
  {N : Subgroup (preE7NonPairAction w i) // N.Normal}

/-! ## The two audited finite-group inputs -/

/-- The complete degree-nine central-product comparison.  In the source
the comparator is `P × C₂`, where `P` is the four-point projective image;
the interface retains only the faithful six-point action and the exact
complete-weight inequality used by the transfer. -/
structure PreE7DegreeNineCentralProductComparator
    (R : Type*) [Group R] [Finite R] : Type where
  Q : Subgroup (Equiv.Perm (Fin 6))
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  complete_bound : ∀ {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))),
    completeQuotientWeight (R := R) J ≤
      coefficient * completeQuotientWeight (R := Q) J

/-- The complete degree-twenty-five central-`C₄` quotient theorem.  Its
coefficient pays all literal normal strata of the fixed complement. -/
structure PreE7DegreeTwentyFiveCentralFourBound
    (R : Type*) [Group R] [Finite R] : Type where
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  complete_bound : ∀ {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))),
    completeQuotientWeight (R := R) J ≤
      coefficient * (2 : ℝ) ^ ((Real.logb 2 48 / 2) * b)

/-! ## Shared literal affine quotient transport -/

private theorem mapped_normal_ne_bot
    {w p d : ℕ} {i : PreE7NonPairActionClass w}
    [Fact p.Prime]
    {R : Subgroup (AffineModel.GLV p d)}
    (e : preE7NonPairAction w i ≃* AffineModel.Aff R)
    (N : NormalAxis i) (hN : N.1 ≠ ⊥) :
    N.1.map e.toMonoidHom ≠ ⊥ := by
  intro hb
  apply hN
  rw [eq_bot_iff]
  intro x hx
  have hm : e x ∈ N.1.map e.toMonoidHom := ⟨x, hx, rfl⟩
  rw [hb] at hm
  exact (Subgroup.mem_bot).mpr
    (e.injective ((Subgroup.mem_bot).mp hm |>.trans (map_one _).symm))

/-! ## Degree nine -/

/-- A literal degree-nine primitive affine action together with its audited
projective central-product comparator. -/
structure PreE7SaprimDegreeNineSource
    (w : ℕ) (i : PreE7NonPairActionClass w) : Type where
  R : Subgroup (AffineModel.GLV 3 2)
  irreducible : AffineModel.Irreducible R
  length : AffineModel.DerivedLength R
  equiv : preE7NonPairAction w i ≃* AffineModel.Aff R
  width_eq : w = 9
  comparator : PreE7DegreeNineCentralProductComparator R
  main_menu : ∀ b,
    (Nat.card (NormalAxis i) : ℝ) * comparator.coefficient ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  tail_menu : ∀ b,
    (Nat.card (AffineModel.Aff R ≃* AffineModel.Aff R) : ℝ) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)

namespace PreE7SaprimDegreeNineSource

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (S : PreE7SaprimDegreeNineSource w i)

private theorem affine_epi_le {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (AffineModel.Aff S.R)) : ℝ) ≤
      (Nat.card (AffineModel.Aff S.R ≃* AffineModel.Aff S.R) : ℝ) *
        (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  simpa using
    ((AffineModel.target S.irreducible S.length (by norm_num : 0 < 2)).epi_card_le_prime
      (J := J))

include S in
private theorem comparator_window :
    preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - ((max 2 6 : ℕ) : ℝ)) / 8 := by
  rw [S.width_eq]
  norm_num [preE7CharacterRho, evenWidth, halfDegree]

/-- Every nonbottom affine axis is first transported to a literal quotient
of `R`, then bounded by the one complete central-product statistic. -/
def axis (N : NormalAxis i) :
    PreE7SmallAxisCertificate (preE7NonPairAction w i) N S.comparator.Q
      (Real.logb 2 3 / 3) := by
  by_cases hN : N.1 = ⊥
  · refine .tail (Nat.card (AffineModel.Aff S.R ≃* AffineModel.Aff S.R))
      (Nat.cast_nonneg _) ?_
    intro b J
    let e : (preE7NonPairAction w i ⧸ N.1) ≃* AffineModel.Aff S.R :=
      (QuotientGroup.quotientMulEquivOfEq hN).trans
        (QuotientGroup.quotientBot.trans S.equiv)
    rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e]
    exact S.affine_epi_le J
  · let N' : Subgroup (AffineModel.Aff S.R) := N.1.map S.equiv.toMonoidHom
    haveI hN' : N'.Normal := N.2.map _ S.equiv.surjective
    have hN'b : N' ≠ ⊥ := mapped_normal_ne_bot S.equiv N hN
    have hker : (SemidirectProduct.rightHom : AffineModel.Aff S.R →* S.R).ker ≤ N' := by
      rw [← SemidirectProduct.range_inl_eq_ker_rightHom]
      exact AffineModel.Vsub_le_normal S.irreducible N' hN'b
    let M : Subgroup S.R := N'.map SemidirectProduct.rightHom
    haveI hM : M.Normal := hN'.map _ SemidirectProduct.rightHom_surjective
    let e : (preE7NonPairAction w i ⧸ N.1) ≃* (S.R ⧸ M) :=
      (QuotientGroup.congr N.1 N' S.equiv rfl).trans
        (quotientEquivOfKerLe SemidirectProduct.rightHom
          SemidirectProduct.rightHom_surjective N' hker)
    refine .bounded S.comparator.coefficient 0
      S.comparator.coefficient_nonneg le_rfl ?_
    intro b J _
    rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e]
    calc
      (Nat.card (GroupEpimorphism J (S.R ⧸ M)) : ℝ) ≤
          completeQuotientWeight (R := S.R) J :=
        card_groupEpimorphism_le_completeQuotientWeight J
          ⟨M, inferInstance⟩ (MulEquiv.refl _)
      _ ≤ S.comparator.coefficient *
          completeQuotientWeight (R := S.comparator.Q) J :=
        S.comparator.complete_bound J
      _ = S.comparator.coefficient *
            completeQuotientWeight (R := S.comparator.Q) J +
          0 * (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by ring

private theorem axis_mainCoefficient_le (N : NormalAxis i) :
    (S.axis N).mainCoefficient ≤ S.comparator.coefficient := by
  by_cases hN : N.1 = ⊥ <;>
    simp [axis, hN, PreE7SmallAxisCertificate.mainCoefficient,
      S.comparator.coefficient_nonneg]

private theorem axis_tailCoefficient_le (N : NormalAxis i) :
    (S.axis N).tailCoefficient ≤
      if N.1 = ⊥ then
        (Nat.card (AffineModel.Aff S.R ≃* AffineModel.Aff S.R) : ℝ) else 0 := by
  by_cases hN : N.1 = ⊥ <;>
    simp [axis, hN, PreE7SmallAxisCertificate.tailCoefficient]

def toData : PreE7SmallAdditiveData w i where
  R := S.comparator.Q
  degree := 6
  action := S.comparator.Q.subtype
  action_injective := Subtype.val_injective
  tailSlope := Real.logb 2 3 / 3
  comparator_window := S.comparator_window
  tail_window := logThreeThird_le_window (by rw [S.width_eq]; norm_num)
  axis := S.axis

/-- Complete numerical SAPRIM data for all certified degree-nine soluble
primitive affine actions. -/
noncomputable def numericalData :
    PreE7SmallAdditiveNumericalData .saprim w i where
  data := S.toData
  main_total_bound := by
    intro b
    unfold fusionAxisEnvelopeTotal
    calc
      (∑ N : NormalAxis i, ((S.toData).certificate .saprim).C b N) ≤
          ∑ _N : NormalAxis i, S.comparator.coefficient := by
        apply Finset.sum_le_sum
        intro N _
        exact S.axis_mainCoefficient_le N
      _ = (Nat.card (NormalAxis i) : ℝ) * S.comparator.coefficient := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := S.main_menu b
  tail_total_bound := by
    intro b
    unfold fusionAxisEnvelopeTotal
    let B : NormalAxis i := ⟨⊥, inferInstance⟩
    calc
      (∑ N : NormalAxis i,
          ((S.toData).certificate .saprim).tailCoefficient b N) ≤
          ∑ N : NormalAxis i,
            if N = B then
              (Nat.card (AffineModel.Aff S.R ≃* AffineModel.Aff S.R) : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro N _
        have hiff : N = B ↔ N.1 = ⊥ := ⟨
          fun hn => by simpa [B] using congrArg Subtype.val hn,
          fun hn => Subtype.ext (by simpa [B] using hn)⟩
        simpa only [hiff] using S.axis_tailCoefficient_le N
      _ = (Nat.card (AffineModel.Aff S.R ≃* AffineModel.Aff S.R) : ℝ) := by
        simp [B]
      _ ≤ _ := S.tail_menu b

end PreE7SaprimDegreeNineSource

/-! ## Degree twenty-five -/

/-- A literal degree-twenty-five primitive affine action together with the
audited complete central-`C₄` quotient bound for its complement. -/
structure PreE7SaprimDegreeTwentyFiveSource
    (w : ℕ) (i : PreE7NonPairActionClass w) : Type where
  R : Subgroup (AffineModel.GLV 5 2)
  irreducible : AffineModel.Irreducible R
  length : AffineModel.DerivedLength R
  equiv : preE7NonPairAction w i ≃* AffineModel.Aff R
  width_eq : w = 25
  centralFour : PreE7DegreeTwentyFiveCentralFourBound R
  tail_menu : ∀ b,
    (Nat.card (AffineModel.Aff R ≃* AffineModel.Aff R) : ℝ) +
        (Nat.card (NormalAxis i) : ℝ) * centralFour.coefficient ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)

namespace PreE7SaprimDegreeTwentyFiveSource

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (S : PreE7SaprimDegreeTwentyFiveSource w i)

private theorem three_logFortyEight_lt_seventeen :
    3 * Real.logb 2 48 < 17 := by
  have hp : ((48 : ℝ) ^ 3) < (2 : ℝ) ^ (17 : ℕ) := by norm_num
  have hl := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by norm_num) 3) hp
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    mul_one] at hl
  exact_mod_cast hl

include S in
private theorem tail_window :
    Real.logb 2 48 / 2 ≤ preE7CharacterWindow w := by
  have hlog := three_logFortyEight_lt_seventeen
  rw [S.width_eq]
  unfold preE7CharacterWindow preE7CharacterRho halfDegree
  norm_num at hlog ⊢
  linarith

private theorem affine_epi_le {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (AffineModel.Aff S.R)) : ℝ) ≤
      (Nat.card (AffineModel.Aff S.R ≃* AffineModel.Aff S.R) : ℝ) *
        (2 : ℝ) ^ ((Real.logb 2 48 / 2) * b) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h :=
    (AffineModel.target S.irreducible S.length (by norm_num : 0 < 2)).epi_card_le_prime
      (J := J)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg b)
  calc
    Real.logb 2 5 / 5 ≤ Real.logb 2 3 / 3 :=
      primeLogSlope_le_three (by norm_num)
    _ ≤ Real.logb 2 48 / 2 := logThreeThird_le_logHalf (by norm_num)

/-- Every axis is a pure tail.  The bottom uses the sharp affine-head bound;
all nonbottom axes are first transported to a literal quotient of `R` and
then absorbed by the complete central-`C₄` theorem. -/
def axis (N : NormalAxis i) :
    PreE7SmallAxisCertificate (preE7NonPairAction w i) N PUnit
      (Real.logb 2 48 / 2) := by
  by_cases hN : N.1 = ⊥
  · refine .tail (Nat.card (AffineModel.Aff S.R ≃* AffineModel.Aff S.R))
      (Nat.cast_nonneg _) ?_
    intro b J
    let e : (preE7NonPairAction w i ⧸ N.1) ≃* AffineModel.Aff S.R :=
      (QuotientGroup.quotientMulEquivOfEq hN).trans
        (QuotientGroup.quotientBot.trans S.equiv)
    rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e]
    exact S.affine_epi_le J
  · refine .tail S.centralFour.coefficient
      S.centralFour.coefficient_nonneg ?_
    intro b J
    let N' : Subgroup (AffineModel.Aff S.R) := N.1.map S.equiv.toMonoidHom
    haveI hN' : N'.Normal := N.2.map _ S.equiv.surjective
    have hN'b : N' ≠ ⊥ := mapped_normal_ne_bot S.equiv N hN
    have hker : (SemidirectProduct.rightHom : AffineModel.Aff S.R →* S.R).ker ≤ N' := by
      rw [← SemidirectProduct.range_inl_eq_ker_rightHom]
      exact AffineModel.Vsub_le_normal S.irreducible N' hN'b
    let M : Subgroup S.R := N'.map SemidirectProduct.rightHom
    haveI hM : M.Normal := hN'.map _ SemidirectProduct.rightHom_surjective
    let e : (preE7NonPairAction w i ⧸ N.1) ≃* (S.R ⧸ M) :=
      (QuotientGroup.congr N.1 N' S.equiv rfl).trans
        (quotientEquivOfKerLe SemidirectProduct.rightHom
          SemidirectProduct.rightHom_surjective N' hker)
    rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e]
    exact (card_groupEpimorphism_le_completeQuotientWeight J
      ⟨M, inferInstance⟩ (MulEquiv.refl _)).trans
        (S.centralFour.complete_bound J)

private theorem axis_mainCoefficient (N : NormalAxis i) :
    (S.axis N).mainCoefficient = 0 := by
  by_cases hN : N.1 = ⊥ <;>
    simp [axis, hN, PreE7SmallAxisCertificate.mainCoefficient]

private theorem axis_tailCoefficient_le (N : NormalAxis i) :
    (S.axis N).tailCoefficient ≤
      (if N.1 = ⊥ then
        (Nat.card (AffineModel.Aff S.R ≃* AffineModel.Aff S.R) : ℝ) else 0) +
        S.centralFour.coefficient := by
  by_cases hN : N.1 = ⊥ <;>
    simp [axis, hN, PreE7SmallAxisCertificate.tailCoefficient,
      S.centralFour.coefficient_nonneg]

def toData : PreE7SmallAdditiveData w i where
  R := PUnit
  degree := 0
  action := 1
  action_injective := fun _ _ _ => Subsingleton.elim _ _
  tailSlope := Real.logb 2 48 / 2
  comparator_window := trivialSmallComparatorWindow (by rw [S.width_eq]; norm_num)
  tail_window := S.tail_window
  axis := S.axis

/-- Complete numerical SAPRIM data for all certified degree-twenty-five
soluble primitive affine actions. -/
noncomputable def numericalData :
    PreE7SmallAdditiveNumericalData .saprim w i where
  data := S.toData
  main_total_bound := by
    intro b
    unfold fusionAxisEnvelopeTotal
    have hz :
        (∑ N : NormalAxis i, ((S.toData).certificate .saprim).C b N) = 0 := by
      apply Finset.sum_eq_zero
      intro N _
      exact S.axis_mainCoefficient N
    rw [hz]
    exact Real.rpow_nonneg (by norm_num) _
  tail_total_bound := by
    intro b
    unfold fusionAxisEnvelopeTotal
    let B : NormalAxis i := ⟨⊥, inferInstance⟩
    calc
      (∑ N : NormalAxis i,
          ((S.toData).certificate .saprim).tailCoefficient b N) ≤
          ∑ N : NormalAxis i,
            ((if N = B then
                (Nat.card (AffineModel.Aff S.R ≃* AffineModel.Aff S.R) : ℝ) else 0) +
              S.centralFour.coefficient) := by
        apply Finset.sum_le_sum
        intro N _
        have hiff : N = B ↔ N.1 = ⊥ := ⟨
          fun hn => by simpa [B] using congrArg Subtype.val hn,
          fun hn => Subtype.ext (by simpa [B] using hn)⟩
        simpa only [hiff] using S.axis_tailCoefficient_le N
      _ = (Nat.card (AffineModel.Aff S.R ≃* AffineModel.Aff S.R) : ℝ) +
          (Nat.card (NormalAxis i) : ℝ) * S.centralFour.coefficient := by
        rw [Finset.sum_add_distrib]
        simp [B, Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := S.tail_menu b

end PreE7SaprimDegreeTwentyFiveSource

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
