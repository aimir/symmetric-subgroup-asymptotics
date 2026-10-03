import SymmetricSubgroupAsymptotics.Non2PreE7RankTailSourceDichotomyClosure
import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveNumerics
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelNumerics
import SymmetricSubgroupAsymptotics.FiniteGroupPaddedGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixTailSource

/-!
# A retained action as its own small comparator

If the abstract ambient group has a faithful permutation representation of
degree smaller than its retained physical degree, every literal normal
quotient is already a quotient of that one comparator.  This gives a cold
source with coefficient one and no extension tail.  The construction is
useful for bounded affine block cells: it uses an alternative faithful
action of the same group and never changes the retained physical weight.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

private abbrev NormalAxis {w : ℕ} (U : PreE7NonPairActionClass w) :=
  {N : Subgroup (preE7NonPairAction w U) // N.Normal}

/-- Data showing that the retained ambient group itself is an admissible
small comparator in another faithful permutation representation. -/
structure PreE7SelfComparatorSource
    (w : ℕ) (U : PreE7NonPairActionClass w) : Type where
  degree : ℕ
  degree_two : 2 ≤ degree
  action : preE7NonPairAction w U →* Equiv.Perm (Fin degree)
  action_injective : Function.Injective action
  exponent_margin : preE7CharacterRho * w ≤
    ((evenWidth w : ℝ) - degree) / 8
  tail_window : (0 : ℝ) ≤ preE7CharacterWindow w
  normal_menu : ∀ b,
    (Nat.card (NormalAxis U) : ℝ) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)

namespace PreE7SelfComparatorSource

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  (S : PreE7SelfComparatorSource w U)

/-- Every literal normal quotient is a quotient of the same abstract
ambient comparator. -/
def axis (_S : PreE7SelfComparatorSource w U) (N : NormalAxis U) :
    PreE7SmallAxisCertificate
      (preE7NonPairAction w U) N (preE7NonPairAction w U) 0 :=
  .comparator ⟨N.1, N.2⟩ (MulEquiv.refl _)

/-- The common small-additive data, with neither a cohomological exponent
nor an additive tail. -/
def data : PreE7SmallAdditiveData w U where
  R := preE7NonPairAction w U
  degree := S.degree
  action := S.action
  action_injective := S.action_injective
  tailSlope := 0
  comparator_window := by
    simpa [max_eq_right S.degree_two] using S.exponent_margin
  tail_window := S.tail_window
  axis := S.axis

private theorem mainCoefficient_eq_one (b : ℕ) (N : NormalAxis U) :
    ((S.data).certificate .acert).C b N = 1 := rfl

private theorem tailCoefficient_eq_zero (b : ℕ) (N : NormalAxis U) :
    ((S.data).certificate .acert).tailCoefficient b N = 0 := rfl

/-- The self-comparator as a numerically complete ordinary source. -/
noncomputable def numericalData :
    PreE7SmallAdditiveNumericalData .acert w U where
  data := S.data
  main_total_bound := by
    intro b
    unfold fusionAxisEnvelopeTotal
    simp_rw [S.mainCoefficient_eq_one b]
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Fintype.card_eq_nat_card] using S.normal_menu b
  tail_total_bound := by
    intro b
    unfold fusionAxisEnvelopeTotal
    simp_rw [S.tailCoefficient_eq_zero b]
    simp
    positivity

/-- Final source used by the affine exceptional-cell dispatcher. -/
noncomputable def toRankTailSourceOrYonedaTop :
    PreE7RankTailSourceOrYonedaTopData w U :=
  .inl (.ordinary .acert (.small S.numericalData))

end PreE7SelfComparatorSource

namespace DegreeSixSelfComparatorSource

variable (U : PreE7NonPairActionClass 6)

/-- The normal menu of any six-point ambient group fits the fixed
subquadratic coefficient allowance. -/
theorem normal_menu (b : ℕ) :
    (Nat.card (NormalAxis U) : ℝ) ≤
      (2 : ℝ) ^
        (16 * (6 : ℝ) * Real.log ((6 + b + 2 : ℕ) : ℝ) ^ 2) := by
  have horder : Nat.card (preE7NonPairAction 6 U) ≤ 2 ^ 10 :=
    (degreeSix_subgroup_and_quotient_order_le
      (preE7NonPairAction 6 U) ⊥).1
  have hnormal : Nat.card (NormalAxis U) ≤ 2 ^ 100 := by
    simpa using normalSubgroup_card_le_two_pow_sq 10 horder
  calc
    (Nat.card (NormalAxis U) : ℝ) ≤ ((2 ^ 100 : ℕ) : ℝ) := by
      exact_mod_cast hnormal
    _ = (2 : ℝ) ^ (100 : ℕ) := by norm_num
    _ = (2 : ℝ) ^ (100 : ℝ) := (Real.rpow_natCast 2 100).symm
    _ ≤ (2 : ℝ) ^ (36 * (6 : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      norm_num
    _ ≤ _ := two_rpow_thirtySix_width_le_menuMass (w := 6) (by norm_num) b

/-- At physical width six, every faithful representation of the same group
on two, three, four, or five points is an admissible self-comparator. -/
noncomputable def source
    (degree : ℕ) (hdegree_two : 2 ≤ degree) (hdegree_five : degree ≤ 5)
    (action : preE7NonPairAction 6 U →* Equiv.Perm (Fin degree))
    (haction : Function.Injective action) :
    PreE7RankTailSourceOrYonedaTopData 6 U :=
  (PreE7SelfComparatorSource.mk degree hdegree_two action haction (by
      have hd : (degree : ℝ) ≤ 5 := by exact_mod_cast hdegree_five
      norm_num [preE7CharacterRho, evenWidth, halfDegree]
      linarith) (by
        norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree])
      (normal_menu U)).toRankTailSourceOrYonedaTop

end DegreeSixSelfComparatorSource

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
