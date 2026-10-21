import SymmetricSubgroupAsymptotics.CyclicAndZGroupCompleteQuotientEnvelope
import SymmetricSubgroupAsymptotics.SemisimpleOuterSmallMultiplierAllowance
import SymmetricSubgroupAsymptotics.Non2PreE7CompleteSourceRankTailBridge

/-! The primitive degree-nine residual with a cyclic order-eight socle
quotient uses KP on every original quotient axis. Its full normal-menu
coefficient is at most2^8, absorbed by the proved outer-factor allowance. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
namespace PrimitiveNineCyclicEightSource

attribute [-instance] originalNormalFintype
open SemisimpleOuterSmallMultiplierAllowance

variable {i : PreE7NonPairActionClass 9}
    (E : Subgroup (preE7NonPairAction 9 i)) [E.Normal]
abbrev Q := preE7NonPairAction 9 i ⧸ E

def eta : ℝ := Real.logb 2 3/3
def degree : ℕ := paddedComparatorDegree preE7CharacterRho 2 9
def delta : ℝ := paddedComparatorDelta preE7CharacterRho eta 2 9
def cutoff : ℝ := (degree : ℝ)/8 + delta/2

private theorem eta_nonneg : 0 ≤ eta := by
  unfold eta
  exact div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)

private theorem eta_le_two_thirds : eta ≤ (2/3 : ℝ) := by
  have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≤ 2^(2 : ℕ))
  simp only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one] at h
  norm_num at h
  unfold eta
  linarith

theorem axis_card_bound (h8 : Nat.card (Q E) = 8) :
    (Nat.card (CyclicAndZGroupCompleteQuotientEnvelope.NormalAxis (Q E)) : ℝ) ≤
      (2 : ℝ)^(24 : ℝ) := by
  letI : Fintype (Q E) := Fintype.ofFinite _
  have hinj : Function.Injective
      (fun N : CyclicAndZGroupCompleteQuotientEnvelope.NormalAxis (Q E) => (N.1 : Set (Q E))) := by
    intro M N h
    exact Subtype.ext (SetLike.coe_injective h)
  have hn := Nat.card_le_card_of_injective _ hinj
  have hs : Nat.card (Set (Q E)) = 2^(Nat.card (Q E)) := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_set]
  rw [hs,h8] at hn
  have hn' : Nat.card (CyclicAndZGroupCompleteQuotientEnvelope.NormalAxis (Q E)) ≤ 2^24 :=
    hn.trans (by decide)
  calc
    _ ≤ (2 : ℝ)^(24 : ℕ) := by exact_mod_cast hn'
    _ = _ := (Real.rpow_natCast (2 : ℝ) 24).symm

def completeSourceData [IsCyclic (Q E)] (C : SemisimpleNormalChart E)
    (h8 : Nat.card (Q E) = 8) (hKP : KovacsPraegerAbelianizationBound)
    (hOuter : SemisimpleOuterFactorPermutationBound) :
    PreE7SemisimpleDirectCompleteSourceData .comp 9 i where
  E := E
  chart := C
  v := degree
  coefficient := fun b =>
    (Nat.card (CyclicAndZGroupCompleteQuotientEnvelope.NormalAxis (Q E)) : ℝ)*coefficient C b
  eta := eta
  delta := delta
  cutoff := cutoff
  alpha := eta+cutoff
  theta := 0
  alpha_eq := rfl
  coefficient_nonneg b := mul_nonneg (Nat.cast_nonneg _) (coefficient_nonneg C b)
  parameters := by
    exact preE7Padded_entryParameters (w := 9) (v0 := 2) eta_nonneg (by decide)
      (by
        have h := eta_le_two_thirds
        norm_num [preE7CharacterRho,evenWidth,halfDegree]
        linarith)
  coefficient_bound b := multiplier_coefficient_bound C (by decide : 6 ≤ 9) hOuter
    (axis_card_bound E h8) b
  combined_bound b J := by
    have hq := CyclicAndZGroupCompleteQuotientEnvelope.cyclic_complete_weight_le
      (G := Q E) hKP J
    have hf := outer_le_coefficient C b J
    have hc := coefficient_nonneg C b
    have hqn : 0 ≤ completeQuotientWeight (R := Q E) J := completeQuotientWeight_nonneg J
    calc
      completeQuotientWeight (R := Q E) J *
          C.outerFactor (Real.logb 2 (Nat.card J)) ≤
          completeQuotientWeight (R := Q E) J * coefficient C b :=
        mul_le_mul_of_nonneg_left hf hqn
      _ ≤ ((Nat.card (CyclicAndZGroupCompleteQuotientEnvelope.NormalAxis (Q E)) : ℝ)*
          (2 : ℝ)^(eta*(b : ℝ)))*coefficient C b :=
        mul_le_mul_of_nonneg_right hq hc
      _ = _ := by ring

def toRankTailOwnerSource [IsCyclic (Q E)] (C : SemisimpleNormalChart E)
    (h8 : Nat.card (Q E) = 8) (hKP : KovacsPraegerAbelianizationBound)
    (hOuter : SemisimpleOuterFactorPermutationBound) :
    PreE7RankTailOwnerSourceData 9 i :=
  (completeSourceData E C h8 hKP hOuter).toRankTailOwnerSource

end PrimitiveNineCyclicEightSource
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
