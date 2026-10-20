import SymmetricSubgroupAsymptotics.ScalarFourCentralSymmetricCompleteQuotientEnvelopeTwo
import SymmetricSubgroupAsymptotics.ScalarFourCentralCompleteQuotientEnvelopeTwo

/-! The actual rank-two geometry gives order at most 2^9, so its complete
quotient sum has ample room for adjoining the separate proper-center
branch. All original quotient axes are still included. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
open Non2UnipotentPrefixFiniteMenu
variable {Q T : Type} [Group Q] [Group T] [Finite Q] [Finite T] {c d : ℕ}
  (D : ScalarFourCentralTopCoordinates Q T c d)

include D in
theorem rank_two_order_le_nine (hT : Nat.card T≤6) (hc : c≤2) (hd : d≤2) :
    Nat.card Q≤2^9 := by
  have h := D.order_le
  have h1 := Nat.pow_le_pow_right (by decide : 1≤2) hc
  have h2 := Nat.pow_le_pow_right (by decide : 1≤4) hd
  have hm := Nat.mul_le_mul h1 h2
  norm_num at hm ⊢
  nlinarith

theorem symmetricColdCoefficient_nine_le (e : T ≃* Equiv.Perm (Fin 3)) :
    symmetricColdCoefficient T 9≤(2 : ℝ)^(80 : ℕ) := by
  have hc : Nat.card T=6 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_perm,Nat.card_fin]; norm_num
  have ha : Nat.card (T ≃* T)≤46656 := by
    calc
      _ ≤ Nat.card (T → T) := Nat.card_le_card_of_injective
        (fun e : T ≃* T => (e : T → T)) DFunLike.coe_injective
      _ = _ := by rw [Nat.card_fun,hc]; norm_num
  have ha' : (Nat.card (T ≃* T) : ℝ)≤46656 := by exact_mod_cast ha
  unfold symmetricColdCoefficient
  exact (mul_le_mul_of_nonneg_right ha' (by positivity)).trans (by norm_num)

theorem symmetric_complete_quotient_envelope_two_tight
    (e : T ≃* Equiv.Perm (Fin 3))
    (hc : c≤2) (hd : d≤2) (hcubic : orderOf D.cubic=3)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), completeQuotientWeight (R := Q) J) ≤
      (2 : ℝ)^(256 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)+
        BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(81 : ℕ)) 15 b := by
  have hsum := D.symmetric_complete_quotient_summed_count_two e hc hd hcubic hZmud lit 9
    (D.rank_two_order_le_nine (by
      rw [Nat.card_congr e.toEquiv,Nat.card_perm,Nat.card_fin]; norm_num) hc hd) b
  have hn : (Nat.card {N : Subgroup Q // N.Normal} : ℝ)≤(2 : ℝ)^(81 : ℕ) := by
    exact_mod_cast normalSubgroup_card_le_two_pow_sq 9 (D.rank_two_order_le_nine (by
      rw [Nat.card_congr e.toEquiv,Nat.card_perm,Nat.card_fin]; norm_num) hc hd)
  have ha : (2 : ℝ)^(coldSlopeTwo*b)≤(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
      (mul_le_mul_of_nonneg_right coldSlopeTwo_le_width_twelve (by positivity))
  have hz : (2 : ℝ)^((51/50 : ℝ)*(b : ℝ))≤(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
      (mul_le_mul_of_nonneg_right (by norm_num : (51/50 : ℝ)≤43/30) (by positivity))
  have hAa : symmetricColdCoefficient T 9*(2 : ℝ)^(coldSlopeTwo*b)≤
      (2 : ℝ)^(80 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) :=
    mul_le_mul (symmetricColdCoefficient_nine_le e) ha (by positivity) (by positivity)
  have hcold : (Nat.card {N : Subgroup Q // N.Normal} : ℝ)*
      ((subgroupCount b : ℝ)*(symmetricColdCoefficient T 9*(2 : ℝ)^(coldSlopeTwo*b)+
        (2 : ℝ)^((51/50 : ℝ)*(b : ℝ)))) ≤
      (2 : ℝ)^(256 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ) := by
    calc
      _ ≤ (2 : ℝ)^(81 : ℕ)*((subgroupCount b : ℝ)*
          ((2 : ℝ)^(80 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))+
            (2 : ℝ)^((43/30 : ℝ)*(b : ℝ)))) :=
        mul_le_mul hn (mul_le_mul_of_nonneg_left (add_le_add hAa hz) (by positivity))
          (by unfold symmetricColdCoefficient; positivity) (by positivity)
      _ = ((2 : ℝ)^(81 : ℕ)*((2 : ℝ)^(80 : ℕ)+1))*
          ((2 : ℝ)^((43/30 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)) := by ring
      _ ≤ _ := by
        have hnum : (2 : ℝ)^(81 : ℕ)*((2 : ℝ)^(80 : ℕ)+1)≤(2 : ℝ)^(256 : ℕ) := by norm_num
        calc
          _ ≤ (2 : ℝ)^(256 : ℕ)*
              ((2 : ℝ)^((43/30 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)) :=
            mul_le_mul_of_nonneg_right hnum (by positivity)
          _ = _ := (mul_assoc _ _ _).symm
  have hhot : (Nat.card {N : Subgroup Q // N.Normal} : ℝ)*
      BinaryKernelRankTailNumerics.raw 1 (9+6) b≤
      BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(81 : ℕ)) 15 b := by
    have hh := mul_le_mul_of_nonneg_right hn
      (show 0≤BinaryKernelRankTailNumerics.raw 1 15 b by
        unfold BinaryKernelRankTailNumerics.raw; positivity)
    simpa only [BinaryKernelRankTailNumerics.raw,one_mul,mul_assoc] using hh
  exact hsum.trans (by rw [mul_add,add_comm]; exact add_le_add hcold hhot)



theorem cubicColdCoefficient_nine_le : cubicColdCoefficient 9≤(2 : ℝ)^(80 : ℕ) := by
  have hp : ((2 : ℝ)^9)^3≤((2 : ℝ)^16)^3 :=
    pow_le_pow_left₀ (by positivity)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (by decide : 9≤16)) 3
  have hh : cubicColdCoefficient 9≤cubicColdCoefficient 16 :=
    mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)
  exact hh.trans (cubicColdCoefficient_sixteen_le.trans
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (by decide : 64≤80)))

theorem complete_quotient_envelope_two_tight
    (D : ScalarFourCentralTopCoordinates Q CyclicThree c d)
    (hc : c≤2) (hd : d≤2) (hcubic : D.cubic=Multiplicative.ofAdd (1 : ZMod 3))
    (f : CyclicThree →* Equiv.Perm (Fin 3)) (hf : Function.Injective f)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), completeQuotientWeight (R := Q) J) ≤
      (2 : ℝ)^(256 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)+
        BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(81 : ℕ)) 12 b := by
  have hsum := D.complete_quotient_summed_count_two hc hd hcubic f hf hZmud lit 9
    (D.rank_two_order_le_nine (by
      rw [Nat.card_congr Multiplicative.toAdd,Nat.card_zmod]; norm_num) hc hd) b
  have hn : (Nat.card {N : Subgroup Q // N.Normal} : ℝ)≤(2 : ℝ)^(81 : ℕ) := by
    exact_mod_cast normalSubgroup_card_le_two_pow_sq 9 (D.rank_two_order_le_nine (by
      rw [Nat.card_congr Multiplicative.toAdd,Nat.card_zmod]; norm_num) hc hd)
  have ha : (2 : ℝ)^(coldSlopeTwo*b)≤(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
      (mul_le_mul_of_nonneg_right coldSlopeTwo_le_width_twelve (by positivity))
  have hz : (2 : ℝ)^((1 : ℝ)*(b : ℝ))≤(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
      (mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ)≤43/30) (by positivity))
  have hAa : cubicColdCoefficient 9*(2 : ℝ)^(coldSlopeTwo*b)≤
      (2 : ℝ)^(80 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) :=
    mul_le_mul (cubicColdCoefficient_nine_le) ha (by positivity) (by positivity)
  have hcold : (Nat.card {N : Subgroup Q // N.Normal} : ℝ)*
      ((subgroupCount b : ℝ)*(cubicColdCoefficient 9*(2 : ℝ)^(coldSlopeTwo*b)+
        (2 : ℝ)^((1 : ℝ)*(b : ℝ)))) ≤
      (2 : ℝ)^(256 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ) := by
    calc
      _ ≤ (2 : ℝ)^(81 : ℕ)*((subgroupCount b : ℝ)*
          ((2 : ℝ)^(80 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))+
            (2 : ℝ)^((43/30 : ℝ)*(b : ℝ)))) :=
        mul_le_mul hn (mul_le_mul_of_nonneg_left (add_le_add hAa hz) (by positivity))
          (by unfold cubicColdCoefficient; positivity) (by positivity)
      _ = ((2 : ℝ)^(81 : ℕ)*((2 : ℝ)^(80 : ℕ)+1))*
          ((2 : ℝ)^((43/30 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)) := by ring
      _ ≤ _ := by
        have hnum : (2 : ℝ)^(81 : ℕ)*((2 : ℝ)^(80 : ℕ)+1)≤(2 : ℝ)^(256 : ℕ) := by norm_num
        calc
          _ ≤ (2 : ℝ)^(256 : ℕ)*
              ((2 : ℝ)^((43/30 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)) :=
            mul_le_mul_of_nonneg_right hnum (by positivity)
          _ = _ := (mul_assoc _ _ _).symm
  have hhot : (Nat.card {N : Subgroup Q // N.Normal} : ℝ)*
      BinaryKernelRankTailNumerics.raw 1 (9+3) b≤
      BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(81 : ℕ)) 12 b := by
    have hh := mul_le_mul_of_nonneg_right hn
      (show 0≤BinaryKernelRankTailNumerics.raw 1 12 b by
        unfold BinaryKernelRankTailNumerics.raw; positivity)
    simpa only [BinaryKernelRankTailNumerics.raw,one_mul,mul_assoc] using hh
  exact hsum.trans (by rw [mul_add,add_comm]; exact add_le_add hcold hhot)



end SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
