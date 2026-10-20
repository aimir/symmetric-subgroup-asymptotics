import SymmetricSubgroupAsymptotics.MarkedC4KernelRankTailNumerics
import SymmetricSubgroupAsymptotics.ExponentialScalarBoundAdd
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairSummedSource
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelNumerics

/-! Combine binary and full C4 kernel tails in the same physical source.
The source sum must retain every original normal quotient. The local marked
moment argument is proved from ordinary published inputs before the final
T1 application; it is not a new literature assumption. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
namespace MixedKernelRankTailResidual

variable {w : ℕ} {U : PreE7NonPairActionClass w}

/-- The only mathematical input is the original complete-source sum. -/
structure Data (w : ℕ) (U : PreE7NonPairActionClass w) : Type where
  cold : ℝ
  theta : ℝ
  hotBinary : ℝ
  factorialPowerBinary : ℕ
  hotC4 : ℝ
  factorialPowerC4 : ℕ
  cold_nonneg : 0 ≤ cold
  hotBinary_nonneg : 0 ≤ hotBinary
  hotC4_nonneg : 0 ≤ hotC4
  cold_le : cold ≤ (2 : ℝ)^(512 : ℕ)
  width : w=12 ∨ w=16
  tail_gap : theta ≤ (halfDegree w : ℝ)/4-preE7CharacterRho*w/4
  summed : ∀ (b : ℕ) (P : Subgroup (preE7NonPairAction w U × Equiv.Perm (Fin b)) → Prop),
    (∑ J : Subgroup (Equiv.Perm (Fin b)), fusionCompleteSourceSum (preE7NonPairAction w U) P J) ≤
      cold*(2 : ℝ)^(theta*b)*(subgroupCount b : ℝ)+
        (BinaryKernelRankTailNumerics.raw hotBinary factorialPowerBinary b +
          MarkedC4KernelRankTailNumerics.raw hotC4 factorialPowerC4 b)

namespace Data
variable (D : Data w U)

def source : PreE7DegreeTwoPairSummedSource w U where
  R := Unit
  v := 1
  action := 1
  action_injective := fun _ _ _ => Subsingleton.elim _ _
  mainCoefficient := 0
  coldCoefficient := fun _ => D.cold
  eta := 0
  theta := D.theta
  mainCoefficient_nonneg := le_rfl
  coldCoefficient_nonneg := fun _ => D.cold_nonneg
  exceptionalRaw := fun b =>
    BinaryKernelRankTailNumerics.raw D.hotBinary D.factorialPowerBinary b +
      MarkedC4KernelRankTailNumerics.raw D.hotC4 D.factorialPowerC4 b
  exceptionalRaw_nonneg := by
    intro b
    have hh := D.hotBinary_nonneg
    have h4 := D.hotC4_nonneg
    have hm : 0 ≤ markedC4Moment b (MarkedC4KernelRankTailNumerics.tilt b) := by
      unfold markedC4Moment
      exact Finset.sum_nonneg (fun _ _ => by positivity)
    unfold BinaryKernelRankTailNumerics.raw MarkedC4KernelRankTailNumerics.raw
    positivity
  summed := by
    intro b P
    simpa only [zero_mul,zero_add,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,Fintype.card_eq_nat_card,subgroupCount,mul_comm,mul_left_comm,mul_assoc]
      using D.summed b P

private theorem parameters :
    PreE7CharacterEntryParameters preE7CharacterRho w 1 0
      (preE7CharacterRho*w/2) (1/8+preE7CharacterRho*w/4)
      (1/8+preE7CharacterRho*w/4) D.theta := by
  have ht := D.tail_gap
  rcases D.width with h | h <;> subst w <;> constructor <;>
    norm_num [preE7CharacterRho,halfDegree] at * <;> assumption

/-- One constructor covers both width12 and16, with the original divisor. -/
def numericalMargin (hM4 : GlobalMarkedC4MomentBound) : D.source.AdditiveNumericalMargin where
  D := fun _ => (2 : ℝ)^(512 : ℕ)
  T := fun _ => (2 : ℝ)^(512 : ℕ)
  eta := 0
  theta := D.theta
  delta := preE7CharacterRho*w/2
  cutoff := 1/8+preE7CharacterRho*w/4
  alpha := 1/8+preE7CharacterRho*w/4
  alpha_eq := by ring
  D_nonneg := fun _ => by positivity
  T_nonneg := fun _ => by positivity
  T_le_D := fun _ => le_rfl
  width_upper := by rcases D.width with h|h <;> omega
  parameters := D.parameters
  total_growth := by
    intro b
    have hw : 8 ≤ w := by rcases D.width with h|h <;> omega
    calc
      _ = (2 : ℝ)^(512 : ℝ) := by norm_num
      _ ≤ (2 : ℝ)^(64*(w : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have : (8 : ℝ) ≤ w := by exact_mod_cast hw
        linarith
      _ ≤ _ := two_rpow_sixtyFour_width_le_menuMass hw b
  summed := by
    intro b P
    apply (D.source.summed b P).trans
    refine add_le_add ?_ (le_refl _)
    apply Finset.sum_le_sum
    intro J _
    change 0*(2 : ℝ)^(0*(b : ℝ))*completeQuotientWeight (R := Unit) J+
      D.cold*(2 : ℝ)^(D.theta*b) ≤ _
    have hm : 0 ≤ ((2 : ℝ)^(512 : ℕ)*(2 : ℝ)^(0*(b : ℝ)))*
        completeQuotientWeight (R := Unit) J := by
      exact mul_nonneg (by positivity) (completeQuotientWeight_nonneg J)
    have ht := mul_le_mul_of_nonneg_right D.cold_le
      (show 0 ≤ (2 : ℝ)^(D.theta*b) by positivity)
    simp only [zero_mul,Real.rpow_zero,mul_one] at hm
    simp only [zero_mul,zero_add,Real.rpow_zero,mul_one]
    exact ht.trans (le_add_of_nonneg_left hm)
  exceptional := by
    intro hc
    have ha : (1 : ℝ) ≤ Nat.card (Subgroup.normalizer
        (preE7NonPairAction w U : Set (Equiv.Perm (Fin w)))) := by
      exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
        (preE7NonPairAction w U : Set (Equiv.Perm (Fin w)))))
    have hh : 6 ≤ w/2 := by rcases D.width with h|h <;> omega
    have hw : 2*(w/2)=w := by rcases D.width with h|h <;> omega
    have E := BinaryKernelRankTailNumerics.exponentialBound hc (w/2) D.factorialPowerBinary
      hh _ D.hotBinary ha D.hotBinary_nonneg
    have F := MarkedC4KernelRankTailNumerics.exponentialBound hM4 (w/2) D.factorialPowerC4
      hh _ D.hotC4 ha D.hotC4_nonneg
    have heq : D.source.exceptionalScalar = (fun b =>
        BinaryKernelRankTailNumerics.pointed (w/2)
          (Nat.card (Subgroup.normalizer
            (preE7NonPairAction w U : Set (Equiv.Perm (Fin w)))) : ℝ)
          D.hotBinary D.factorialPowerBinary b +
        MarkedC4KernelRankTailNumerics.pointed (w/2)
          (Nat.card (Subgroup.normalizer
            (preE7NonPairAction w U : Set (Equiv.Perm (Fin w)))) : ℝ)
          D.hotC4 D.factorialPowerC4 b) := by
      funext b
      change growingQuotientNormalizedPointing b w _ *
          (BinaryKernelRankTailNumerics.raw D.hotBinary D.factorialPowerBinary b +
            MarkedC4KernelRankTailNumerics.raw D.hotC4 D.factorialPowerC4 b) =
        growingQuotientNormalizedPointing b (2*(w/2)) _ *
          BinaryKernelRankTailNumerics.raw D.hotBinary D.factorialPowerBinary b +
        growingQuotientNormalizedPointing b (2*(w/2)) _ *
          MarkedC4KernelRankTailNumerics.raw D.hotC4 D.factorialPowerC4 b
      rw [hw,mul_add]
    rw [heq]
    exact E.add F

def residualChoice (hM4 : GlobalMarkedC4MomentBound) : PreE7NumericalRankTailResidualChoice w U :=
  D.source.toResidualChoiceAdditive (D.numericalMargin hM4)

def finalSource (hM4 : GlobalMarkedC4MomentBound) : PreE7RankTailSourceOrYonedaTopData w U :=
  .inr (.inr (D.residualChoice hM4))

end Data
end MixedKernelRankTailResidual
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
