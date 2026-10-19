import SymmetricSubgroupAsymptotics.BinaryKernelRankTailResidual
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairSummedSource
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelNumerics

/-! Install a proved cold/hot complete-source sum at width16 with a larger fixed coefficient.
No source estimate or catalogue coverage is assumed to be published here:
the caller must prove the literal physical source sum. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
namespace WidthSixteenBinaryRankTailResidual

/-- At width sixteen the original menu envelope pays a fixed coefficient
up to `2^(100w)`, uniformly in the later source degree. -/
theorem two_rpow_hundred_width_le_menuMass {w : ℕ} (hw : 16 ≤ w) (b : ℕ) :
    (2 : ℝ) ^ (100 * (w : ℝ)) ≤
      (2 : ℝ) ^ (16 * (w : ℝ) * Real.log ((w+b+2 : ℕ) : ℝ)^2) := by
  have heq : Real.exp (5/2 : ℝ)^2=Real.exp 5 := by
    rw [pow_two,←Real.exp_add]
    congr 1
    norm_num
  have heq5 : Real.exp (5 : ℝ)=Real.exp 1^5 := by
    rw [←Real.exp_nat_mul]
    congr 1
    norm_num
  have he5 : Real.exp (5 : ℝ)<(3 : ℝ)^5 := by
    rw [heq5]
    exact pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos _).le (by decide)
  have he : Real.exp (5/2 : ℝ)<18 := by
    nlinarith [Real.exp_pos (5/2 : ℝ)]
  have ha : (18 : ℝ)≤((w+b+2 : ℕ) : ℝ) := by exact_mod_cast (show 18≤w+b+2 by omega)
  have hl : (5/2 : ℝ)≤Real.log ((w+b+2 : ℕ) : ℝ) :=
    ((Real.lt_log_iff_exp_lt (by positivity)).2 (he.trans_le ha)).le
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hn : (0 : ℝ)≤w := Nat.cast_nonneg w
  have hs : (25/4 : ℝ)≤Real.log ((w+b+2 : ℕ) : ℝ)^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hs hn
  nlinarith

variable {w : ℕ} {U : PreE7NonPairActionClass w}

/-- The only mathematical input is the original complete-source sum. -/
structure Data (w : ℕ) (U : PreE7NonPairActionClass w) : Type where
  cold : ℝ
  theta : ℝ
  hot : ℝ
  factorialPower : ℕ
  cold_nonneg : 0 ≤ cold
  hot_nonneg : 0 ≤ hot
  cold_le : cold ≤ (2 : ℝ)^(1280 : ℕ)
  width : w=16
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
  have hw := D.width
  subst w
  constructor <;> norm_num [preE7CharacterRho,halfDegree] at * <;> assumption

/-- One constructor covers both width12 and16, with the original divisor. -/
def numericalMargin : D.source.AdditiveNumericalMargin where
  D := fun _ => (2 : ℝ)^(1280 : ℕ)
  T := fun _ => (2 : ℝ)^(1280 : ℕ)
  eta := 0
  theta := D.theta
  delta := preE7CharacterRho*w/2
  cutoff := 1/8+preE7CharacterRho*w/4
  alpha := 1/8+preE7CharacterRho*w/4
  alpha_eq := by ring
  D_nonneg := fun _ => by positivity
  T_nonneg := fun _ => by positivity
  T_le_D := fun _ => le_rfl
  width_upper := by have hw := D.width; omega
  parameters := D.parameters
  total_growth := by
    intro b
    have hw : 16 ≤ w := by have hw := D.width; omega
    calc
      _ = (2 : ℝ)^(1280 : ℝ) := by norm_num
      _ ≤ (2 : ℝ)^(100*(w : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have : (16 : ℝ) ≤ w := by exact_mod_cast hw
        linarith
      _ ≤ _ := two_rpow_hundred_width_le_menuMass hw b
  summed := by
    intro b P
    apply (D.source.summed b P).trans
    refine add_le_add ?_ (le_refl _)
    apply Finset.sum_le_sum
    intro J _
    change 0*(2 : ℝ)^(0*(b : ℝ))*completeQuotientWeight (R := Unit) J+
      D.cold*(2 : ℝ)^(D.theta*b) ≤ _
    have hm : 0 ≤ ((2 : ℝ)^(1280 : ℕ)*(2 : ℝ)^(0*(b : ℝ)))*
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
    have hh : 6 ≤ w/2 := by have hw := D.width; omega
    have hw : 2*(w/2)=w := by have hw := D.width; omega
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
end WidthSixteenBinaryRankTailResidual
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
