import SymmetricSubgroupAsymptotics.OriginalBinaryAffineThreeComplementInterval
import SymmetricSubgroupAsymptotics.BinaryGeneralLinearSmallExactMultiplicities
import SymmetricSubgroupAsymptotics.TinyBinaryLowerCeilingCertificates

/-! The remaining one-dimensional and three-dimensional tiny binary family on the
literal original action. Its exact same-order coefficients imply the
ordinary kernel budgets used by the shared scalar certificate. No group
catalogue or stronger top bound is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyBinaryLowerStep
open OriginalAffineBlockCharacteristicHead OriginalBinaryAffineExactChooseDivisorCost
open OriginalBinaryAffineDominantDivisorCost (totalMultiplicity)
open BinaryGeneralLinearMatchingPrimeMultiplicity

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem genRank_le_ceiling_of_three_mul_binary (hp : P.p = 2)
    (hd : translationDimension J block P = 1 ∨ translationDimension J block P = 3)
    (i : block.Points) (a : ℕ) (ha2 : 2 ≤ a) (ha5 : a ≤ 5)
    (hshape : Fintype.card block.Points = 3*2^a)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let t := Fintype.card block.Points
  let d := translationDimension J block P
  let C : ℝ := totalMultiplicity d
  let m : ℝ := matchingMultiplicity d 2
  have hd' : d = 1 ∨ d = 3 := hd
  have hm0 : 0 ≤ m := by positivity
  have hdiv2 : 2^a ∣ t := by
    rw [show t = 3*2^a from hshape]
    exact ⟨3,by ring⟩
  have hdiv3 : 3^1 ∣ t := by
    rw [show t = 3*2^a from hshape]
    exact ⟨2^a,by simp⟩
  have hcost0 : (MarkedC4.genRank J : ℝ) ≤
      (t : ℝ)*(m*min (ActualWreathChooseDivisorCapacity.primaryRate 2 a) (1/3)+
        (C-m)/(2 : ℝ)^a)+MarkedC4.genRank block.Top := by
    have hh := genRank_le_two_divisor_rates J block P hp i 2 a 3 1
      Nat.prime_two hdiv2 (by decide) hdiv3 (by decide)
    calc
      _ ≤ twoDivisorCost d t 2 a 3 1+MarkedC4.genRank block.Top := hh
      _ = _ := by
        dsimp only [twoDivisorCost,C,m]
        norm_num only [pow_one,Nat.cast_ofNat]
        ring
  have hmin := mul_le_mul_of_nonneg_left
    (min_le_right (ActualWreathChooseDivisorCapacity.primaryRate 2 a) (1/3 : ℝ)) hm0
  have hcost : (MarkedC4.genRank J : ℝ) ≤
      (t : ℝ)*(m/3+(C-m)/(2 : ℝ)^a)+MarkedC4.genRank block.Top := by
    have hh := hcost0.trans (add_le_add (mul_le_mul_of_nonneg_left (add_le_add hmin le_rfl)
      (show (0 : ℝ) ≤ t by positivity)) le_rfl)
    convert hh using 1 <;> ring
  have htEq : (t : ℝ) = 3*(2 : ℝ)^a := by exact_mod_cast hshape
  have hhead : (t : ℝ)*(m/3+(C-m)/(2 : ℝ)^a) =
      (TinyBinaryLowerCeilingCertificates.headCut d a : ℝ) := by
    rcases hd' with hdEq | hdEq
    · have hC1 : C = 1 := by
        dsimp only [C]
        rw [hdEq,BinaryGeneralLinearSmallExactMultiplicities.totalMultiplicity_eq 1 (by decide)]
        norm_num [BinaryGeneralLinearSmallExactMultiplicities.smallTotal]
      have hm1 : m = 1 := by
        dsimp only [m]
        rw [hdEq,BinaryGeneralLinearSmallExactMultiplicities.matching_two_eq]
        norm_num
      rw [hC1,hm1,htEq]
      simp only [TinyBinaryLowerCeilingCertificates.headCut,if_pos hdEq,Nat.cast_pow,Nat.cast_ofNat]
      ring
    · have hC8 : C = 8 := by
        dsimp only [C]
        rw [hdEq,BinaryGeneralLinearSmallExactMultiplicities.totalMultiplicity_eq 3 (by decide)]
        norm_num [BinaryGeneralLinearSmallExactMultiplicities.smallTotal]
      have hm6 : m = 6 := by
        dsimp only [m]
        rw [hdEq,BinaryGeneralLinearSmallExactMultiplicities.matching_two_eq]
        norm_num
      rw [hC8,hm6,htEq]
      simp only [TinyBinaryLowerCeilingCertificates.headCut,if_neg (show d ≠ 1 by omega),
        Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
      field_simp [(by positivity : (2 : ℝ)^a ≠ 0)] <;> ring
  have htopR : (MarkedC4.genRank block.Top : ℝ) ≤ (traceyPermutationGeneratorCeiling t : ℝ) := by
    exact_mod_cast (show MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling t by
      simpa only [t,Fintype.card_eq_nat_card] using htop)
  have hcostNat : MarkedC4.genRank J ≤
      TinyBinaryLowerCeilingCertificates.headCut d a+traceyPermutationGeneratorCeiling (3*2^a) := by
    rw [hhead] at hcost
    have hh := hcost.trans (add_le_add le_rfl htopR)
    rw [show t = 3*2^a from hshape] at hh
    exact_mod_cast hh
  have hscalar := TinyBinaryLowerCeilingCertificates.aggregate_small d a (MarkedC4.genRank J)
    hd' ha2 ha5 hcostNat
  have hn : n = 3*2^(a+d) := by
    calc
      n = Nat.card block.Fibre*Nat.card block.Points := by
        simpa only [Nat.card_fin] using block.degree_product.symm
      _ = 2^d*(3*2^a) := by
        rw [fibre_card_eq_prime_pow_dimension J block P,hp]
        simp only [d,Fintype.card_eq_nat_card] at hshape ⊢
        rw [hshape]
      _ = 3*2^(a+d) := by rw [pow_add]; ring
  exact hscalar.trans_eq (congrArg traceyPermutationGeneratorCeiling hn).symm

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyBinaryLowerStep
