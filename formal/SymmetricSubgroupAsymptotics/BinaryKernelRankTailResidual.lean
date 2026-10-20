import SymmetricSubgroupAsymptotics.BinaryKernelRankTailNumerics
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairSummedSource
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelNumerics

/-! Install a proved cold/hot complete-source sum at width12 or16.
No source estimate or catalogue coverage is assumed to be published here:
the caller must prove the literal physical source sum. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
namespace BinaryKernelRankTailResidual

variable {w : ℕ} {U : PreE7NonPairActionClass w}

/-- The only mathematical input is the original complete-source sum. -/
structure Data (w : ℕ) (U : PreE7NonPairActionClass w) : Type where
  cold : ℝ
  theta : ℝ
  hot : ℝ
  factorialPower : ℕ
  cold_nonneg : 0 ≤ cold
  hot_nonneg : 0 ≤ hot
  cold_le : cold ≤ (2 : ℝ)^(512 : ℕ)
  width : w=12 ∨ w=16
  tail_gap : theta ≤ (halfDegree w : ℝ)/4-preE7CharacterRho*w/4
  summed : ∀ (b : ℕ) (P : Subgroup (preE7NonPairAction w U × Equiv.Perm (Fin b)) → Prop),
    (∑ J : Subgroup (Equiv.Perm (Fin b)), fusionCompleteSourceSum (preE7NonPairAction w U) P J) ≤
      cold*(2 : ℝ)^(theta*b)*(subgroupCount b : ℝ)+
        BinaryKernelRankTailNumerics.raw hot factorialPower b

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
  exceptionalRaw := BinaryKernelRankTailNumerics.raw D.hot D.factorialPower
  exceptionalRaw_nonneg := by
    intro b
    have hh := D.hot_nonneg
    unfold BinaryKernelRankTailNumerics.raw
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
def numericalMargin : D.source.AdditiveNumericalMargin where
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
    have heq : D.source.exceptionalScalar =
        BinaryKernelRankTailNumerics.pointed (w/2)
          (Nat.card (Subgroup.normalizer
            (preE7NonPairAction w U : Set (Equiv.Perm (Fin w)))) : ℝ)
          D.hot D.factorialPower := by
      funext b
      change growingQuotientNormalizedPointing b w _ *
          BinaryKernelRankTailNumerics.raw D.hot D.factorialPower b =
        growingQuotientNormalizedPointing b (2*(w/2)) _ *
          BinaryKernelRankTailNumerics.raw D.hot D.factorialPower b
      rw [hw]
    rw [heq]
    exact BinaryKernelRankTailNumerics.exponentialBound hc (w/2) D.factorialPower
      hh _ D.hot ha D.hot_nonneg

def residualChoice : PreE7NumericalRankTailResidualChoice w U :=
  D.source.toResidualChoiceAdditive D.numericalMargin

def finalSource : PreE7RankTailSourceOrYonedaTopData w U :=
  .inr (.inr D.residualChoice)

end Data
end BinaryKernelRankTailResidual
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
