import SymmetricSubgroupAsymptotics.OriginalBinaryAffineJointCharacteristicCost
import SymmetricSubgroupAsymptotics.OriginalBinaryAffineTraceyWedgeStep
import SymmetricSubgroupAsymptotics.BinaryAffineJointBoundedWindows

/-! An actual original-action binary affine induction step with exact
scalar exceptions. The genuine smaller top is the only generator bound
assumed. The paid Boolean is a concrete seven-pair numerical guard, not
a desired generator inequality or a group classification certificate.
No assertion is made for non-power-of-two top degrees or unpaid pairs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineJointWindowStep
open OriginalAffineBlockCharacteristicHead BinaryAffineJointSelectedWindowNumerics
open NaturalSquareRootQuotientCeiling BinaryAffineJointBoundedWindows

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem genRank_le_jointCost (hp : P.p = 2) (e : ℕ) (he : 1 ≤ e)
    (ht : Fintype.card block.Points = 2^e) (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ jointCost (translationDimension J block P) e := by
  let d := translationDimension J block P
  have htcard : Nat.card block.Points = 2^e := by
    simpa only [Fintype.card_eq_nat_card] using ht
  have hlog : Real.logb 2 ((2 : ℝ)^e) = (e : ℝ) := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  have htop' : MarkedC4.genRank block.Top ≤ ⌈(2 : ℝ)^e/Real.sqrt e⌉₊ := by
    simpa only [traceyPermutationGeneratorCeiling, htcard, Nat.cast_pow,
      Nat.cast_ofNat, hlog] using htop
  have htopR : (MarkedC4.genRank block.Top : ℝ) ≤
      (⌈(2 : ℝ)^e/Real.sqrt e⌉₊ : ℕ) := by exact_mod_cast htop'
  have hcost := OriginalBinaryAffineJointCharacteristicCost.genRank_le_joint_primary_cost
    J block P hp e ht i
  have hcostEq := congrArg (fun k : ℕ => (k : ℝ))
    (jointCost_eq_actual d e (by omega))
  simp only [Nat.cast_add, Nat.cast_mul] at hcostEq hcost
  have hcostR : (MarkedC4.genRank J : ℝ) ≤ (jointCost d e : ℝ) := by
    change (MarkedC4.genRank J : ℝ) ≤
      ((d : ℝ) + ((d*(d-1)/2 : ℕ) : ℝ))*(e.choose (e/2) : ℝ) +
        (Nat.log 2 (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))) -
          d*(d-1)/2 : ℕ) + MarkedC4.genRank block.Top at hcost
    nlinarith
  exact_mod_cast hcostR

/-- All binary affine defining-primary steps outside seven exact scalar
pairs are proved, with the original source degree and actual top. -/
theorem genRank_le_ceiling_outside_unpaid (hp : P.p = 2) (e : ℕ) (he : 1 ≤ e)
    (ht : Fintype.card block.Points = 2^e) (i : block.Points)
    (hpaid : unpaid (translationDimension J block P) e = false)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let d := translationDimension J block P
  by_cases hregion : 10 ≤ d ∨ (20 ≤ e ∧ 12*d ≤ e)
  · exact OriginalBinaryAffineTraceyWedgeStep.genRank_le_ceiling
      J block P hp e he ht i hregion htop
  · have hd : 1 ≤ d := by
      have hf := fibre_card_eq_prime_pow_dimension J block P
      have htwo := block.degrees_ge_two.1
      rw [hp] at hf
      by_contra! hh
      have hz : d = 0 := by omega
      change Nat.card block.Fibre = 2^d at hf
      rw [hz, pow_zero] at hf
      omega
    have hd9 : d ≤ 9 := by omega
    have hew : e < max 20 (12*d) := by omega
    have hnum := bounded_window_le d e hd hd9 he hew hpaid
    have hsource := genRank_le_jointCost J block P hp e he ht i htop
    have hn : n = 2^(d+e) := by
      calc
        n = Nat.card block.Fibre * Nat.card block.Points := by
          simpa only [Nat.card_fin] using block.degree_product.symm
        _ = 2^d * 2^e := by
          rw [fibre_card_eq_prime_pow_dimension J block P, hp,
            show Nat.card block.Points = 2^e by
              simpa only [Fintype.card_eq_nat_card] using ht]
        _ = _ := (pow_add _ _ _).symm
    have hlog : Real.logb 2 ((2 : ℝ)^(d+e)) = (d+e : ℕ) := by
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
    have hceil : quotientCeiling (2^(d+e)) (d+e) =
        traceyPermutationGeneratorCeiling n := by
      rw [quotientCeiling_eq _ _ (by omega)]
      simp only [traceyPermutationGeneratorCeiling, hn, Nat.cast_pow, Nat.cast_ofNat, hlog]
    exact (hsource.trans hnum).trans_eq hceil

theorem exists_generating_finset (hp : P.p = 2) (e : ℕ) (he : 1 ≤ e)
    (ht : Fintype.card block.Points = 2^e) (i : block.Points)
    (hpaid : unpaid (translationDimension J block P) e = false)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧
      S.card ≤ traceyPermutationGeneratorCeiling n := by
  obtain ⟨S, hcard, hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨S, hgen, hcard.le.trans
    (genRank_le_ceiling_outside_unpaid J block P hp e he ht i hpaid htop)⟩

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineJointWindowStep
