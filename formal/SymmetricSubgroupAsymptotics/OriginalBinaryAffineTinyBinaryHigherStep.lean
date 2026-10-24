import SymmetricSubgroupAsymptotics.OriginalBinaryAffineThreeComplementInterval
import SymmetricSubgroupAsymptotics.BinaryGeneralLinearOddSmallStrictMultiplicities
import SymmetricSubgroupAsymptotics.TinyComplementHigherEnvelopes
import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate

/-! The entire higher-dimensional tiny binary-primary family on the
original action. Its top degree is three times its actual binary divisor;
the actual two-divisor cost and exact ceiling rounding are retained.
Only the genuine smaller-top ceiling is an inductive hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyBinaryHigherStep
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
    (hd4 : 4 ≤ translationDimension J block P) (hd6 : translationDimension J block P ≤ 6)
    (i : block.Points) (a : ℕ) (ha2 : 2 ≤ a) (ha5 : a ≤ 5)
    (hshape : Fintype.card block.Points = 3*2^a)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let t := Fintype.card block.Points
  let d := translationDimension J block P
  let C : ℝ := totalMultiplicity d
  let m : ℝ := matchingMultiplicity d 2
  have hd4' : 4 ≤ d := hd4
  have hd6' : d ≤ 6 := hd6
  have ht : 2 ≤ t := by
    simpa only [t,Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have ht0 : t ≠ 0 := by omega
  have hm0 : 0 ≤ m := by positivity
  have hmC : m ≤ C := by
    have hh := pair_factorizations_le_cardFactors
      (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))) 2 3 (by decide)
    have hn : matchingMultiplicity d 2 ≤ totalMultiplicity d := by
      unfold matchingMultiplicity totalMultiplicity
      simp only [if_true]
      omega
    dsimp only [m,C]
    exact_mod_cast hn
  have hC : C ≤ (d : ℝ)^2-2 := by
    have hn := BinaryGeneralLinearOddSmallStrictMultiplicities.total_le_square_sub_two d hd4' hd6'
    have hR : (totalMultiplicity d : ℝ) ≤ ((d^2-2 : ℕ) : ℝ) := by exact_mod_cast hn
    have hdSq : 2 ≤ d^2 := by nlinarith only [Nat.mul_le_mul hd4' hd4']
    simpa only [C,Nat.cast_sub hdSq,Nat.cast_pow,Nat.cast_ofNat] using hR
  have hmA : m ≤ (d : ℝ)*((d : ℝ)+1)/2 := by
    have hh := matchingMultiplicity_le_triangle d 2
    have heven := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self d)
    have hsub : d-1+1 = d := by omega
    have hmul := congrArg (fun x : ℕ => d*x) hsub
    have heq : 2*(d+d*(d-1)/2) = d*(d+1) := by nlinarith only [heven,hmul]
    have heqR : (2 : ℝ)*((d+d*(d-1)/2 : ℕ) : ℝ) = (d : ℝ)*((d : ℝ)+1) := by
      exact_mod_cast heq
    have hhR : m ≤ ((d+d*(d-1)/2 : ℕ) : ℝ) := by
      dsimp only [m]
      exact_mod_cast hh
    linarith only [hhR,heqR]
  have hdiv2 : 2^a ∣ t := by
    rw [show t = 3*2^a from hshape]
    exact ⟨3,by ring⟩
  have hdiv3 : 3^1 ∣ t := by
    rw [show t = 3*2^a from hshape]
    exact ⟨2^a,by simp⟩
  have hcost : (MarkedC4.genRank J : ℝ) ≤
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
  let u := min (ActualWreathChooseDivisorCapacity.primaryRate 2 a) (1/3 : ℝ)
  let L := Real.logb 2 (t : ℝ)
  have hlowpow : 2^(3+2*a) ≤ t^2 := by
    have hp : (2^a : ℕ)^2 = 2^(2*a) := by rw [← pow_mul,Nat.mul_comm a 2]
    rw [show t = 3*2^a from hshape,mul_pow,hp,pow_add]
    exact Nat.mul_le_mul_right _ (by decide : 2^3 ≤ 3^2)
  have hhighpow : t^5 ≤ 2^(8+5*a) := by
    have hp : (2^a : ℕ)^5 = 2^(5*a) := by rw [← pow_mul,Nat.mul_comm a 5]
    rw [show t = 3*2^a from hshape,mul_pow,hp,pow_add]
    exact Nat.mul_le_mul_right _ (by decide : 3^5 ≤ 2^8)
  have hL : (7/2 : ℝ) ≤ L := by
    have hh := IntegerLogSquareRootCeilingCertificate.log_lower t 2 (3+2*a)
      (by omega) (by decide) hlowpow
    have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha2
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hh
    change ((3 : ℝ)+2*(a : ℝ))/2 ≤ L at hh
    linarith only [hh,haR]
  have hLhi : L ≤ (33/5 : ℝ) := by
    have hh := IntegerLogSquareRootCeilingCertificate.log_upper t 5 (8+5*a)
      (by omega) (by decide) hhighpow
    have haR : (a : ℝ) ≤ 5 := by exact_mod_cast ha5
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hh
    change L ≤ ((8 : ℝ)+5*(a : ℝ))/5 at hh
    linarith only [hh,haR]
  have hM4 : 4 ≤ 2^a := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) ha2
    simpa only [show (2 : ℕ)^2 = 4 by decide] using hh
  have hscaled := TinyComplementHigherEnvelopes.binary_envelope_le d hd4'
    ((2 : ℝ)^a) m C u L (by exact_mod_cast hM4) hm0 hmA hmC hC
    (min_le_right _ _) hL hLhi
  have hL0 : 0 < L := by linarith only [hL]
  have hratio : Real.sqrt ((d : ℝ)+L)/Real.sqrt L = Real.sqrt (1+(d : ℝ)/L) := by
    rw [← Real.sqrt_div (by positivity : 0 ≤ (d : ℝ)+L)]
    congr 1
    field_simp [hL0.ne'] <;> ring
  have hscaled' : (m*u+(C-m)/(2 : ℝ)^a+1/(3*(2 : ℝ)^a))*Real.sqrt ((d : ℝ)+L)+
      Real.sqrt ((d : ℝ)+L)/Real.sqrt L ≤ (2 : ℝ)^d := by
    rw [hratio]
    exact hscaled
  have htopR : (MarkedC4.genRank block.Top : ℝ) ≤
      (traceyPermutationGeneratorCeiling t : ℝ) := by
    exact_mod_cast (show MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling t by
      simpa only [t,Fintype.card_eq_nat_card] using htop)
  change (MarkedC4.genRank block.Top : ℝ) ≤
    (⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) at htopR
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hceil : (⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) ≤ (t : ℝ)/Real.sqrt L+1 :=
    (Nat.ceil_lt_add_one (div_nonneg htR.le (Real.sqrt_nonneg _))).le
  have hg : (MarkedC4.genRank J : ℝ) ≤
      (t : ℝ)*(m*u+(C-m)/(2 : ℝ)^a)+(t : ℝ)/Real.sqrt L+1 := by
    change (MarkedC4.genRank J : ℝ) ≤
      (t : ℝ)*(m*u+(C-m)/(2 : ℝ)^a)+MarkedC4.genRank block.Top at hcost
    linarith only [hcost,htopR,hceil]
  have htEq : (t : ℝ) = 3*(2 : ℝ)^a := by exact_mod_cast hshape
  have hs : 0 < Real.sqrt ((d : ℝ)+L) := Real.sqrt_pos.mpr (by positivity)
  have hreal : (MarkedC4.genRank J : ℝ) ≤
      (2 : ℝ)^d*(t : ℝ)/Real.sqrt ((d : ℝ)+L) := by
    apply (le_div_iff₀ hs).mpr
    calc
      (MarkedC4.genRank J : ℝ)*Real.sqrt ((d : ℝ)+L) ≤
          ((t : ℝ)*(m*u+(C-m)/(2 : ℝ)^a)+(t : ℝ)/Real.sqrt L+1)*Real.sqrt ((d : ℝ)+L) :=
        mul_le_mul_of_nonneg_right hg hs.le
      _ = (t : ℝ)*((m*u+(C-m)/(2 : ℝ)^a+1/(3*(2 : ℝ)^a))*Real.sqrt ((d : ℝ)+L)+
          Real.sqrt ((d : ℝ)+L)/Real.sqrt L) := by
        rw [htEq]
        field_simp [(by positivity : (2 : ℝ)^a ≠ 0),(Real.sqrt_pos.mpr hL0).ne'] <;> ring
      _ ≤ (t : ℝ)*(2 : ℝ)^d := mul_le_mul_of_nonneg_left hscaled' htR.le
      _ = (2 : ℝ)^d*(t : ℝ) := mul_comm _ _
  have hn : n = 2^d*t := by
    calc
      n = Nat.card block.Fibre*Nat.card block.Points := by
        simpa only [Nat.card_fin] using block.degree_product.symm
      _ = 2^d*t := by
        rw [fibre_card_eq_prime_pow_dimension J block P,hp]
        simp only [d,t,Fintype.card_eq_nat_card]
  have hnR : (n : ℝ) = (2 : ℝ)^d*(t : ℝ) := by exact_mod_cast hn
  have hlogn : Real.logb 2 (n : ℝ) = (d : ℝ)+Real.logb 2 (t : ℝ) := by
    rw [hnR,Real.logb_mul (by positivity : (2 : ℝ)^d ≠ 0)
      (by exact_mod_cast ht0),Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one]
  have htarget : (MarkedC4.genRank J : ℝ) ≤ (n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ)) := by
    rw [hlogn,hnR]
    exact hreal
  have hfinal := htarget.trans (Nat.le_ceil ((n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ))))
  change (MarkedC4.genRank J : ℝ) ≤ (traceyPermutationGeneratorCeiling n : ℝ) at hfinal
  exact_mod_cast hfinal
end SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyBinaryHigherStep
