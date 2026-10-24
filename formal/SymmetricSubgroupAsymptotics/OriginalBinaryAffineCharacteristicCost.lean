import SymmetricSubgroupAsymptotics.OriginalAffineBlockCharacteristicHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineComplementDefiningValuation
import SymmetricSubgroupAsymptotics.CharacteristicChiefOrderProductBound

/-! A characteristic-sensitive ordinary cost on the SAME original
binary affine block action. The translation head is separated before
charging the actual complement quotient. Thus its off-characteristic
cost is controlled by the complement order, not the full affine order.
No generator estimate for the top, Tracey input, or local census is used.
The only degree specialization is the literal top degree `2^e`. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineCharacteristicCost
open OriginalAffineBlockCharacteristicHead
open ActualWreathCharacteristicChiefProfile ActualWreathChiefOrderDivisibility
open CharacteristicChiefFilteredDimensions CharacteristicChiefPrimePowerCosts

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem translation_quotient_defining_valuation_le :
    (Nat.card (block.Component ⧸ P.V)).factorization P.p ≤
      translationDimension J block P * (translationDimension J block P - 1) / 2 := by
  let x : block.Fibre := ⟨x₀, block.map_base⟩
  let C := P.elementaryChart block.component_preprimitive
  let eqv : (block.Component ⧸ P.V) ≃* P.complement x :=
    (QuotientGroup.quotientMulEquivOfEq (P.complementProjection_ker x).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (P.complementProjection x) (P.complementProjection_surjective x))
  have hc := Nat.card_congr eqv.toEquiv
  rw [hc]
  exact P.complement_defining_valuation_le block.component_preprimitive C x

theorem tail_other_cost_le {c : ℕ}
    (prof : Profile (Fintype.card block.Points) c (Nat.card (block.Component ⧸ P.V)))
    (hp : P.p = 2) :
    (otherDimensionAt 2 prof.charges : ℝ) + prof.simpleRank ≤
      (translationDimension J block P : ℝ)^2 := by
  have hh := CharacteristicChiefOrderProductBound.other_dimensions_rank_le_log_order
    prof 2 Nat.prime_two
  have hc := translation_quotient_card_le J block P
  rw [hp] at hc
  have hcR : (Nat.card (block.Component ⧸ P.V) : ℝ) ≤
      (2 : ℝ)^((translationDimension J block P)^2) := by exact_mod_cast hc
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (show (0 : ℝ) < Nat.card (block.Component ⧸ P.V) by
      exact_mod_cast Nat.card_pos (α := block.Component ⧸ P.V)) hcR
  have hlog' : Real.logb 2 (Nat.card (block.Component ⧸ P.V) : ℝ) ≤
      (translationDimension J block P : ℝ)^2 := by
    simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
      mul_one, Nat.cast_pow] using hlog
  exact hh.trans hlog'

private theorem triangular_cast (d : ℕ) :
    (d : ℝ) + ((d*(d-1)/2 : ℕ) : ℝ) ≤ (d : ℝ)*(d+1)/2 := by
  have hs := Finset.sum_range_succ (fun i : ℕ => i) d
  have htri : d + d*(d-1)/2 = d*(d+1)/2 := by
    calc
      d + d*(d-1)/2 = d*(d-1)/2+d := Nat.add_comm _ _
      _ = (d+1)*d/2 := by
        simpa only [Finset.sum_range_id, Nat.add_sub_cancel] using hs.symm
      _ = d*(d+1)/2 := by rw [Nat.mul_comm (d+1) d]
  calc
    _ = ((d+d*(d-1)/2 : ℕ) : ℝ) := (Nat.cast_add _ _).symm
    _ = ((d*(d+1)/2 : ℕ) : ℝ) := congrArg (fun k : ℕ => (k : ℝ)) htri
    _ ≤ ((d*(d+1) : ℕ) : ℝ)/(2 : ℝ) := Nat.cast_div_le
    _ = _ := by push_cast; rfl

/-- Automatic original-source bound retaining the genuine strictly
smaller top rank. The triangular coefficient and square allowance are
derived here, not supplied as a numerical certificate. -/
theorem genRank_le_primary_cost (hp : P.p = 2) (e : ℕ)
    (ht : Fintype.card block.Points = 2^e) (i : block.Points) :
    (MarkedC4.genRank J : ℝ) ≤
      ((translationDimension J block P : ℝ) * (translationDimension J block P + 1) / 2) *
        (e.choose (e/2) : ℝ) + (translationDimension J block P : ℝ)^2 +
          MarkedC4.genRank block.Top := by
  obtain ⟨c, hc, ⟨prof⟩, hhead, hrank⟩ := exists_translation_head_and_tail J block P i
  have htR : (Fintype.card block.Points : ℝ) = (2 : ℝ)^e := by exact_mod_cast ht
  have cancel (a b : ℝ) : a*(2 : ℝ)^e*b/(2 : ℝ)^e = a*b := by
    rw [mul_right_comm, mul_div_cancel_right₀ _ (by positivity : (2 : ℝ)^e ≠ 0)]
  have hheadCost := (headCharge J block P i).primePower 2 e Nat.prime_two ht
  simp only [show 2-1 = (1 : ℕ) by omega, mul_one, headCharge_dimension] at hheadCost
  rw [htR, cancel] at hheadCost
  have htail := profile_cost_le_primePower_valuation prof 2 e Nat.prime_two ht
    (Nat.card_pos (α := block.Component ⧸ P.V)).ne'
  simp only [show 2-1 = (1 : ℕ) by omega, mul_one] at htail
  rw [htR, cancel] at htail
  have hv := translation_quotient_defining_valuation_le J block P
  rw [hp] at hv
  have hvR : ((Nat.card (block.Component ⧸ P.V)).factorization 2 : ℝ) ≤
      ((translationDimension J block P * (translationDimension J block P - 1) / 2 : ℕ) : ℝ) := by
    exact_mod_cast hv
  have hvMul := mul_le_mul_of_nonneg_right hvR
    (show 0 ≤ (e.choose (e/2) : ℝ) by positivity)
  have hother := tail_other_cost_le J block P prof.toProfile hp
  have hcoeff := mul_le_mul_of_nonneg_right
    (triangular_cast (translationDimension J block P))
    (show 0 ≤ (e.choose (e/2) : ℝ) by positivity)
  have hrankR : (MarkedC4.genRank J : ℝ) ≤
      ((headCharge J block P i).capacity : ℝ) + (c : ℝ) + MarkedC4.genRank block.Top := by
    exact_mod_cast hrank
  nlinarith

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineCharacteristicCost
