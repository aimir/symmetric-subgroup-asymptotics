import SymmetricSubgroupAsymptotics.Non2PreE7SaprimOddCyclicAffine
import SymmetricSubgroupAsymptotics.Non2PreE7SmallOrderSemisimple

/-!
# Large odd primitive affine SAPRIM actions

This module covers the degree-27 row and every odd affine degree at least 49
from one complement-order certificate.  The affine bottom retains the sharp
derived-head slope `log₂(p)/p`.  Every nonbottom literal axis is a quotient
of the linear complement and is counted from a published generating set of
the source permutation group.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

open AffineModel Equiv SemidirectProduct

/-- The sharp affine-head slope is below half the logarithm of any
complement-order ceiling `q ≥ 3`. -/
theorem logThreeThird_le_logHalf {q : ℕ} (hq : 3 ≤ q) :
    Real.logb 2 3 / 3 ≤ Real.logb 2 q / 2 := by
  have hlog0 : 0 ≤ Real.logb 2 3 := Real.logb_nonneg (by norm_num) (by norm_num)
  have hmono : Real.logb 2 3 ≤ Real.logb 2 q := by
    apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by norm_num)
    exact_mod_cast hq
  calc
    Real.logb 2 3 / 3 ≤ Real.logb 2 3 / 2 := by linarith
    _ ≤ Real.logb 2 q / 2 := by linarith

/-- An odd affine action whose linear complement has order at most `q`.
Keeping the literal ceiling is essential at degree 27: the structural theorem
gives `q = 78`, whose slope fits the window, while rounding it to 128 does
not.  For all odd degrees at least 49 the Halasi--Maróti base theorem gives a
polynomial ceiling. -/
structure PreE7SaprimOddLargeAffineSource
    (w : ℕ) (i : PreE7NonPairActionClass w) : Type where
  p : ℕ
  [primeFact : Fact p.Prime]
  three_le : 3 ≤ p
  d : ℕ
  R : Subgroup (AffineModel.GLV p d)
  irreducible : AffineModel.Irreducible R
  length : AffineModel.DerivedLength R
  d_pos : 0 < d
  equiv : preE7NonPairAction w i ≃* AffineModel.Aff R
  q : ℕ
  q_lower : 3 ≤ q
  complement_order_le : Nat.card R ≤ q
  width_lower : 27 ≤ w
  width_upper : w < 1024
  slope_window : Real.logb 2 q / 2 ≤ preE7CharacterWindow w
  tail_menu : ∀ b,
    (Nat.card (AffineModel.Aff R ≃* AffineModel.Aff R) : ℝ) +
        (Nat.card {N : Subgroup (preE7NonPairAction w i) // N.Normal} : ℝ) *
          (q : ℝ) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)

attribute [instance] PreE7SaprimOddLargeAffineSource.primeFact

namespace PreE7SaprimOddLargeAffineSource

variable {w : ℕ} {i : PreE7NonPairActionClass w}

def tailSlope (S : PreE7SaprimOddLargeAffineSource w i) : ℝ :=
  Real.logb 2 S.q / 2

private theorem oddPrimeSlope_le_tailSlope
    (S : PreE7SaprimOddLargeAffineSource w i) :
    Real.logb 2 S.p / S.p ≤ S.tailSlope := by
  calc
    Real.logb 2 S.p / S.p ≤ Real.logb 2 3 / 3 :=
      primeLogSlope_le_three S.three_le
    _ ≤ Real.logb 2 S.q / 2 := logThreeThird_le_logHalf S.q_lower

private theorem bottom_epi_le (S : PreE7SaprimOddLargeAffineSource w i) {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (AffineModel.Aff S.R)) : ℝ) ≤
      (Nat.card (AffineModel.Aff S.R ≃* AffineModel.Aff S.R) : ℝ) *
        (2 : ℝ) ^ (S.tailSlope * b) := by
  have h := (AffineModel.target S.irreducible S.length S.d_pos).epi_card_le_prime
    (J := J)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact mul_le_mul_of_nonneg_right S.oddPrimeSlope_le_tailSlope (Nat.cast_nonneg b)

/-- Generator counting for a target whose order is at most the literal
ceiling `q`.  The additive `+2` in the source generator bound becomes one
coefficient `q`; the remaining slope is exactly `log₂(q)/2`. -/
theorem epi_le_orderCeiling
    (hgen : PermutationSubgroupGeneratorBound)
    {b q : ℕ} (J : Subgroup (Equiv.Perm (Fin b)))
    {Q : Type*} [Group Q] [Finite Q] (hq : 1 ≤ q) (hQ : Nat.card Q ≤ q) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      (q : ℝ) * (2 : ℝ) ^ ((Real.logb 2 q / 2) * b) := by
  obtain ⟨T, hT, hTcard⟩ := hgen b J
  have hepi : Nat.card (GroupEpimorphism J Q) ≤ Nat.card (J →* Q) := by
    letI : Finite (J →* Q) := Finite.of_injective
      (fun f : J →* Q => (f : J → Q)) DFunLike.coe_injective
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hnat : Nat.card (GroupEpimorphism J Q) ≤ q ^ T.card := by
    calc
      Nat.card (GroupEpimorphism J Q) ≤ Nat.card (J →* Q) := hepi
      _ ≤ Nat.card Q ^ T.card := monoidHom_card_le_pow_of_closure T hT
      _ ≤ q ^ T.card := Nat.pow_le_pow_left hQ _
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlog0 : 0 ≤ Real.logb 2 q :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hq)
  have hexp : Real.logb 2 q * (T.card : ℝ) ≤
      Real.logb 2 q + (Real.logb 2 q / 2) * b := by
    have hTcardR : (2 : ℝ) * T.card ≤ b + 2 := by exact_mod_cast hTcard
    nlinarith
  calc
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
        (2 : ℝ) ^ (Real.logb 2 q * (T.card : ℝ)) := by
      calc
        _ ≤ ((q ^ T.card : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = ((q : ℝ) ^ (T.card : ℕ)) := by norm_num
        _ = _ := by
          rw [Real.rpow_mul (by norm_num),
            Real.rpow_logb (by norm_num) (by norm_num) hqR,
            Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^
        (Real.logb 2 q + (Real.logb 2 q / 2) * b) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = _ := by
      rw [Real.rpow_add (by norm_num)]
      rw [Real.rpow_logb (by norm_num) (by norm_num) hqR]

/-- Every literal normal axis is paid by the same source-independent tail. -/
def axis (S : PreE7SaprimOddLargeAffineSource w i)
    (hgen : PermutationSubgroupGeneratorBound)
    (N : {N : Subgroup (preE7NonPairAction w i) // N.Normal}) :
    PreE7SmallAxisCertificate (preE7NonPairAction w i) N PUnit S.tailSlope := by
  by_cases hN : N.1 = ⊥
  · refine .tail (Nat.card (AffineModel.Aff S.R ≃* AffineModel.Aff S.R))
      (Nat.cast_nonneg _) ?_
    intro b J
    let e : (preE7NonPairAction w i ⧸ N.1) ≃* AffineModel.Aff S.R :=
      (QuotientGroup.quotientMulEquivOfEq hN).trans
        (QuotientGroup.quotientBot.trans S.equiv)
    rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e]
    exact S.bottom_epi_le J
  · refine .tail S.q (Nat.cast_nonneg _) ?_
    intro b J
    let N' : Subgroup (AffineModel.Aff S.R) := N.1.map S.equiv.toMonoidHom
    haveI hN' : N'.Normal := N.2.map _ S.equiv.surjective
    have hN'b : N' ≠ ⊥ := by
      intro hb
      apply hN
      rw [eq_bot_iff]
      intro x hx
      have hm : S.equiv x ∈ N' := ⟨x, hx, rfl⟩
      rw [hb] at hm
      exact (Subgroup.mem_bot).mpr
        (S.equiv.injective ((Subgroup.mem_bot).mp hm |>.trans (map_one _).symm))
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
    apply epi_le_orderCeiling hgen J ((by norm_num : 1 ≤ 3).trans S.q_lower)
    exact (Nat.card_le_card_of_surjective _
      (QuotientGroup.mk_surjective (s := M))).trans S.complement_order_le

private theorem axis_mainCoefficient (S : PreE7SaprimOddLargeAffineSource w i)
    (hgen : PermutationSubgroupGeneratorBound)
    (N : {N : Subgroup (preE7NonPairAction w i) // N.Normal}) :
    (S.axis hgen N).mainCoefficient = 0 := by
  by_cases hN : N.1 = ⊥ <;>
    simp [axis, hN, PreE7SmallAxisCertificate.mainCoefficient]

private theorem axis_tailCoefficient_le (S : PreE7SaprimOddLargeAffineSource w i)
    (hgen : PermutationSubgroupGeneratorBound)
    (N : {N : Subgroup (preE7NonPairAction w i) // N.Normal}) :
    (S.axis hgen N).tailCoefficient ≤
      (if N.1 = ⊥ then
        (Nat.card (AffineModel.Aff S.R ≃* AffineModel.Aff S.R) : ℝ) else 0) +
        (S.q : ℝ) := by
  by_cases hN : N.1 = ⊥ <;>
    simp [axis, hN, PreE7SmallAxisCertificate.tailCoefficient]

def toData (S : PreE7SaprimOddLargeAffineSource w i)
    (hgen : PermutationSubgroupGeneratorBound) :
    PreE7SmallAdditiveData w i where
  R := PUnit
  degree := 0
  action := 1
  action_injective := fun _ _ _ => Subsingleton.elim _ _
  tailSlope := S.tailSlope
  comparator_window := trivialSmallComparatorWindow (by
    have := S.width_lower
    omega : 6 ≤ w)
  tail_window := S.slope_window
  axis := S.axis hgen

noncomputable def numericalData (S : PreE7SaprimOddLargeAffineSource w i)
    (hgen : PermutationSubgroupGeneratorBound) :
    PreE7SmallAdditiveNumericalData .saprim w i where
  data := S.toData hgen
  main_total_bound := by
    intro b
    unfold fusionAxisEnvelopeTotal
    have hz :
        (∑ N : {N : Subgroup (preE7NonPairAction w i) // N.Normal},
          ((S.toData hgen).certificate .saprim).C b N) = 0 := by
      apply Finset.sum_eq_zero
      intro N _
      exact S.axis_mainCoefficient hgen N
    rw [hz]
    exact Real.rpow_nonneg (by norm_num) _
  tail_total_bound := by
    intro b
    unfold fusionAxisEnvelopeTotal
    let B : {N : Subgroup (preE7NonPairAction w i) // N.Normal} := ⟨⊥, inferInstance⟩
    calc
      (∑ N : {N : Subgroup (preE7NonPairAction w i) // N.Normal},
          ((S.toData hgen).certificate .saprim).tailCoefficient b N) ≤
          ∑ N : {N : Subgroup (preE7NonPairAction w i) // N.Normal},
            ((if N = B then
                (Nat.card (AffineModel.Aff S.R ≃* AffineModel.Aff S.R) : ℝ) else 0) +
              (S.q : ℝ)) := by
        apply Finset.sum_le_sum
        intro N _
        have h := S.axis_tailCoefficient_le hgen N
        convert h using 1
        congr 2
        exact propext ⟨
          fun hn => by simpa [B] using congrArg Subtype.val hn,
          fun hn => Subtype.ext (by simpa [B] using hn)⟩
      _ = (Nat.card (AffineModel.Aff S.R ≃* AffineModel.Aff S.R) : ℝ) +
          (Nat.card {N : Subgroup (preE7NonPairAction w i) // N.Normal} : ℝ) *
            (S.q : ℝ) := by
        rw [Finset.sum_add_distrib]
        simp [B]
      _ ≤ _ := S.tail_menu b

end PreE7SaprimOddLargeAffineSource

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
