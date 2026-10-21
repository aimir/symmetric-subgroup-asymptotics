import SymmetricSubgroupAsymptotics.NonabelianEightCompleteQuotientReduction
import SymmetricSubgroupAsymptotics.SemisimpleOuterSmallMultiplierAllowance
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveSmallNumerics
import SymmetricSubgroupAsymptotics.Non2PreE7CompleteSourceRankTailBridge

/-! The one-block degree-nine residual with a nonabelian order-eight
socle quotient has a complete mixed source. Proper quotient axes are paid
by the actual central quotient of order four; only the onto-map term uses
one general character. The actual semisimple outer factor is paid once. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
namespace PrimitiveNineNonabelianEightMixedSource

attribute [-instance] originalNormalFintype
open SemisimpleOuterSmallMultiplierAllowance

variable {i : PreE7NonPairActionClass 9}
    (E : Subgroup (preE7NonPairAction 9 i)) [E.Normal]

abbrev Q := preE7NonPairAction 9 i ⧸ E
abbrev R := Q E ⧸ Subgroup.center (Q E)

def degree : ℕ := paddedComparatorDegree preE7CharacterRho (Nat.card (R E)) 9
def delta : ℝ := paddedComparatorDelta preE7CharacterRho 0 (Nat.card (R E)) 9
def cutoff : ℝ := (degree E : ℝ)/8 + delta E/2

def action : R E →* Equiv.Perm (Fin (degree E)) :=
  (characterComparatorPadHom (le_max_left _ _)).comp
    (OuterWreathPermutationCompression.regularAction (R E))

theorem action_injective : Function.Injective (action E) :=
  (characterComparatorPadHom_injective _).comp
    (OuterWreathPermutationCompression.regularAction_injective (R E))

theorem automorphism_card_bound (h8 : Nat.card (Q E) = 8) :
    (Nat.card (Q E ≃* Q E) : ℝ) ≤ (2 : ℝ)^(24 : ℝ) := by
  have hn := Nat.card_le_card_of_injective
    (fun a : Q E ≃* Q E => (a : Q E → Q E)) DFunLike.coe_injective
  rw [Nat.card_fun,h8] at hn
  have hn' : Nat.card (Q E ≃* Q E) ≤ 2^24 := by norm_num at hn ⊢; exact hn
  calc
    (Nat.card (Q E ≃* Q E) : ℝ) ≤ (2 : ℝ)^(24 : ℕ) := by exact_mod_cast hn'
    _ = (2 : ℝ)^(24 : ℝ) := (Real.rpow_natCast (2 : ℝ) 24).symm

theorem tail_slope : Real.logb 2 5/3 ≤ preE7CharacterWindow 9 := by
  have hlog := logb_two_five_div_five_lt_seven_fifteenths
  norm_num [preE7CharacterWindow,preE7CharacterRho,halfDegree]
  linarith

theorem entryParameters (h8 : Nat.card (Q E) = 8)
    (hnc : ¬IsMulCommutative (Q E)) :
    PreE7CharacterEntryParameters preE7CharacterRho 9 (degree E) 0
      (delta E) (cutoff E) (cutoff E) (Real.logb 2 5/3) := by
  have hR : Nat.card (R E) = 4 :=
    NonabelianEightCompleteQuotientReduction.central_quotient_card h8 hnc
  have hp := preE7Padded_entryParameters_withTail (w := 9) (v0 := Nat.card (R E))
    (eta := 0) (theta := Real.logb 2 5/3) (by norm_num) (by rw [hR]; decide)
    (by rw [hR]; norm_num [preE7CharacterRho,evenWidth,halfDegree]) tail_slope
  simpa only [degree,delta,cutoff,zero_add] using hp

variable (C : SemisimpleNormalChart E)

def certificate (h8 : Nat.card (Q E) = 8) (hnc : ¬IsMulCommutative (Q E))
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    PreE7CompleteSourceComparatorCertificate .comp 9 i where
  R := R E
  groupR := inferInstance
  finiteR := inferInstance
  v := degree E
  action := action E
  action_injective := action_injective E
  D := coefficient C
  T := fun b => (Nat.card (Q E ≃* Q E) : ℝ)*coefficient C b
  eta := 0
  delta := delta E
  cutoff := cutoff E
  alpha := cutoff E
  theta := Real.logb 2 5/3
  alpha_eq := by simp
  D_nonneg := coefficient_nonneg C
  T_nonneg := fun b => mul_nonneg (Nat.cast_nonneg _) (coefficient_nonneg C b)
  broad_source_envelope := by
    intro b J
    let U := preE7NonPairAction 9 i
    have hsurvive : fusionCompleteSourceSum U
        (preE7NoPairNoC3BroadActionPredicate 9 i b) J ≤
        ∑ N : {N : Subgroup U // N.Normal},
          (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ) := by
      unfold fusionCompleteSourceSum
      exact Finset.sum_le_sum (fun N _ => fusionSurvivingEpiCount_le_groupEpimorphism_card U
        (preE7NoPairNoC3BroadActionPredicate 9 i b) N J)
    have houter := C.outerSum_le (J := J)
    have hfactor := outer_le_coefficient C b J
    have hweight := NonabelianEightCompleteQuotientReduction.complete_weight_le_character_tail
      h8 hnc hZmud lit J
    have hc : 0 ≤ coefficient C b := coefficient_nonneg C b
    calc
      fusionCompleteSourceSum U
          (preE7NoPairNoC3BroadActionPredicate 9 i b) J ≤
          ∑ N : {N : Subgroup U // N.Normal},
            (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ) := hsurvive
      _ ≤ completeQuotientWeight (R := Q E) J *
          C.outerFactor (Real.logb 2 (Nat.card J)) := by
        simpa only [U,Q,completeQuotientWeight,completeQuotientCount,Nat.cast_sum] using houter
      _ ≤ completeQuotientWeight (R := Q E) J * coefficient C b :=
        mul_le_mul_of_nonneg_left hfactor (completeQuotientWeight_nonneg J)
      _ ≤ ((Nat.card (Q E ≃* Q E) : ℝ)*
          (2 : ℝ)^((Real.logb 2 5/3)*(b : ℝ)) +
          completeQuotientWeight (R := R E) J)*coefficient C b :=
        mul_le_mul_of_nonneg_right hweight hc
      _ = (coefficient C b*(2 : ℝ)^((0 : ℝ)*b))*
          completeQuotientWeight (R := R E) J +
          ((Nat.card (Q E ≃* Q E) : ℝ)*coefficient C b)*
            (2 : ℝ)^((Real.logb 2 5/3)*(b : ℝ)) := by
        simp only [zero_mul,Real.rpow_zero,mul_one]
        ring

def numericalData (h8 : Nat.card (Q E) = 8) (hnc : ¬IsMulCommutative (Q E))
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (hOuter : SemisimpleOuterFactorPermutationBound) :
    PreE7CompleteSourceNumericalData .comp 9 i where
  certificate := certificate E C h8 hnc hZmud lit
  parameters := entryParameters E h8 hnc
  main_total_bound b := by
    have h := multiplier_coefficient_bound C (by decide : 6 ≤ 9) hOuter
      (a := 1) (by norm_num) b
    simpa only [certificate,one_mul] using h
  tail_total_bound b := by
    exact multiplier_coefficient_bound C (by decide : 6 ≤ 9) hOuter
      (automorphism_card_bound E h8) b

def toRankTailOwnerSource (h8 : Nat.card (Q E) = 8) (hnc : ¬IsMulCommutative (Q E))
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (hOuter : SemisimpleOuterFactorPermutationBound) :
    PreE7RankTailOwnerSourceData 9 i :=
  (numericalData E C h8 hnc hZmud lit hOuter).toRankTailOwnerSource

end PrimitiveNineNonabelianEightMixedSource
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
