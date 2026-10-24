import SymmetricSubgroupAsymptotics.OriginalFourPointSharedChooseCost
import SymmetricSubgroupAsymptotics.ActualWreathSixOrderTwoDivisorCost

/-! The actual shared four-point head together with both literal primary
divisors on the SAME order-six quotient trace. The zero odd-image case
has only the translation capacity. The nonzero case shares its positions
before charging the actual quotient. No independent GL2 head/tail or
assumed improvement to the top rank is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalFourPointSharedTwoDivisorCost
open OriginalAffineBlockCharacteristicHead ActualWreathChooseDivisorCapacity

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem genRank_le_zero_odd_two_divisor (hfour : Nat.card block.Fibre = 4)
    (hp : P.p = 2) (hdim : translationDimension J block P = 2)
    (hzero : BinaryPlaneWreathActualOddKernel.oddKernel
      (FourPointBlockAffineCoordinates.linearImage block.map block.map_equivariant block.base hfour) = ⊥)
    (i : block.Points) (a : ℕ) (h2 : 2^a ∣ Fintype.card block.Points)
    (h3 : 3 ∣ Fintype.card block.Points) :
    (MarkedC4.genRank J : ℝ) ≤ 2*(Fintype.card block.Points : ℝ)*
      min (primaryRate 2 a) (1/3)+MarkedC4.genRank block.Top := by
  have hI : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have h31 : 3^1 ∣ Fintype.card block.Points := by simpa only [pow_one] using h3
  have hc := ActualWreathChiefChooseDivisorWeights.layerCapacity_le_min_divisorWeights
    (OriginalBlockOrdinaryCompressionState.initialState J block) (QuotientGroup.mk' P.V)
    (translationChart J block P) i hI 2 a 3 1 Nat.prime_two h2 Nat.prime_three h31
  change ((headCharge J block P i).capacity : ℝ) ≤
    (translationDimension J block P : ℝ)*
      min (divisorWeight (Fintype.card block.Points) 2 a P.p)
        (divisorWeight (Fintype.card block.Points) 3 1 P.p) at hc
  rw [hp,hdim] at hc
  have h22 := divisorWeight_le_divisorRate (Fintype.card block.Points) 2 a 2
    (by omega) Nat.prime_two h2
  have h32 := divisorWeight_le_divisorRate (Fintype.card block.Points) 3 1 2
    (by omega) Nat.prime_three h31
  change divisorWeight (Fintype.card block.Points) 2 a 2 ≤
    (Fintype.card block.Points : ℝ)*primaryRate 2 a at h22
  simp only [divisorRate,if_neg (by decide : (2 : ℕ) ≠ 3),pow_one] at h32
  have ht : (0 : ℝ) ≤ Fintype.card block.Points := by positivity
  have hmin : min (divisorWeight (Fintype.card block.Points) 2 a 2)
      (divisorWeight (Fintype.card block.Points) 3 1 2) ≤
        (Fintype.card block.Points : ℝ)*min (primaryRate 2 a) (1/3) := by
    have hh := min_le_min h22 h32
    simpa only [mul_min_of_nonneg _ _ ht,mul_one_div] using hh
  have hcapacity := hc.trans (mul_le_mul_of_nonneg_left hmin
    (show (0 : ℝ) ≤ (2 : ℕ) by norm_num))
  have hr : (MarkedC4.genRank J : ℝ) ≤ ((headCharge J block P i).capacity : ℝ)+
      MarkedC4.genRank block.Top := by
    exact_mod_cast OriginalFourPointZeroOddCharacteristicCost.genRank_le_head_add_top
      J block P hfour hp hzero i
  have hh := hr.trans (add_le_add hcapacity le_rfl)
  simpa only [Nat.cast_ofNat,mul_assoc] using hh

theorem genRank_le_shared_two_divisor (hfour : Nat.card block.Fibre = 4)
    (hp : P.p = 2) (hdim : translationDimension J block P = 2)
    (i : block.Points) (a : ℕ) (h2 : 2^a ∣ Fintype.card block.Points)
    (h3 : 3 ∣ Fintype.card block.Points) :
    (MarkedC4.genRank J : ℝ) ≤
      max (2*(Fintype.card block.Points : ℝ)*min (primaryRate 2 a) (1/3))
        ((Fintype.card block.Points : ℝ)/2+
          (Fintype.card block.Points : ℝ)*min (primaryRate 2 a) (1/3)+
          (Fintype.card block.Points : ℝ)*min (1/(2 : ℝ)^a) (primaryRate 3 1))+
            MarkedC4.genRank block.Top := by
  classical
  by_cases hzero : BinaryPlaneWreathActualOddKernel.oddKernel
      (FourPointBlockAffineCoordinates.linearImage block.map block.map_equivariant block.base hfour) = ⊥
  · exact (genRank_le_zero_odd_two_divisor J block P hfour hp hdim hzero i a h2 h3).trans
      (add_le_add (le_max_left _ _) le_rfl)
  · have hI : 2 ≤ Fintype.card block.Points := by
      simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2
    have htail := ActualWreathSixOrderTwoDivisorCost.genRank_le_two_divisor_min
      (quotientState J block P) i hI
      (OriginalFourPointSharedChooseCost.quotientState_card_dvd_six J block P hp hdim) a h2 h3
    have hhead := OriginalFourPointSharedTranslationKernel.genRank_le_half_add_quotient
      J block P hfour hp hzero
    have hheadR : (MarkedC4.genRank J : ℝ) ≤ (MarkedC4.genRank (quotientState J block P).A : ℝ)+
        (Nat.card block.Points/2 : ℕ) := by exact_mod_cast hhead
    have hhalf : ((Nat.card block.Points/2 : ℕ) : ℝ) ≤ (Fintype.card block.Points : ℝ)/2 := by
      simpa only [Fintype.card_eq_nat_card] using
        (Nat.cast_div_le (m := Nat.card block.Points) (n := 2) (α := ℝ))
    have hh : (MarkedC4.genRank J : ℝ) ≤ (Fintype.card block.Points : ℝ)/2+
        (Fintype.card block.Points : ℝ)*min (primaryRate 2 a) (1/3)+
          (Fintype.card block.Points : ℝ)*min (1/(2 : ℝ)^a) (primaryRate 3 1)+
            MarkedC4.genRank block.Top := by linarith only [htail,hheadR,hhalf]
    exact hh.trans (add_le_add (le_max_right _ _) le_rfl)

theorem genRank_le_five_sixths_add_primeTo (hfour : Nat.card block.Fibre = 4)
    (hp : P.p = 2) (hdim : translationDimension J block P = 2)
    (i : block.Points) (a : ℕ) (h2 : 2^a ∣ Fintype.card block.Points)
    (h3 : 3 ∣ Fintype.card block.Points) :
    (MarkedC4.genRank J : ℝ) ≤ (5/6 : ℝ)*(Fintype.card block.Points)+
      (Fintype.card block.Points : ℝ)/(2 : ℝ)^a+MarkedC4.genRank block.Top := by
  have hh := genRank_le_shared_two_divisor J block P hfour hp hdim i a h2 h3
  have ht : (0 : ℝ) ≤ Fintype.card block.Points := by positivity
  have hm := mul_le_mul_of_nonneg_left (min_le_right (primaryRate 2 a) (1/3 : ℝ)) ht
  have hn := mul_le_mul_of_nonneg_left (min_le_left (1/(2 : ℝ)^a) (primaryRate 3 1)) ht
  have hz : (0 : ℝ) ≤ (Fintype.card block.Points : ℝ)/(2 : ℝ)^a := by positivity
  have hfirst : 2*(Fintype.card block.Points : ℝ)*min (primaryRate 2 a) (1/3) ≤
      (5/6 : ℝ)*(Fintype.card block.Points)+(Fintype.card block.Points : ℝ)/(2 : ℝ)^a := by
    nlinarith only [hm,ht,hz]
  have hsecond : (Fintype.card block.Points : ℝ)/2+
      (Fintype.card block.Points : ℝ)*min (primaryRate 2 a) (1/3)+
      (Fintype.card block.Points : ℝ)*min (1/(2 : ℝ)^a) (primaryRate 3 1) ≤
        (5/6 : ℝ)*(Fintype.card block.Points)+(Fintype.card block.Points : ℝ)/(2 : ℝ)^a := by
    have hn' : (Fintype.card block.Points : ℝ)*min (1/(2 : ℝ)^a) (primaryRate 3 1) ≤
        (Fintype.card block.Points : ℝ)/(2 : ℝ)^a := by simpa only [mul_one_div] using hn
    linarith only [hm,hn']
  exact hh.trans (add_le_add (max_le hfirst hsecond) le_rfl)

end SymmetricSubgroupAsymptotics.OriginalFourPointSharedTwoDivisorCost
