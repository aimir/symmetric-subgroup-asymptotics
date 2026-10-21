import SymmetricSubgroupAsymptotics.Non2PreE7SmallOrderSemisimple

/-! An actual target of order at most ten has onto-map slope at most5/3
under the retained ordinary permutation generator theorem. The extra
generator in the rounded theorem is kept in the coefficient ten. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

theorem epimorphism_card_le_ten_of_order_le_ten
    {Q : Type} [Group Q] [Finite Q] (hQ : Nat.card Q ≤ 10)
    (hMN : PermutationSubgroupGeneratorBound) (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      10 * (2 : ℝ)^((5/3 : ℝ)*(b : ℝ)) := by
  obtain ⟨S,hS,hScard⟩ := hMN b J
  letI : Finite (J →* Q) := Finite.of_injective
    (fun f : J →* Q => (f : J → Q)) DFunLike.coe_injective
  have hn : Nat.card (GroupEpimorphism J Q) ≤ 10^S.card := calc
    _ ≤ Nat.card (J →* Q) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ ≤ Nat.card Q^S.card := monoidHom_card_le_pow_of_closure S hS
    _ ≤ 10^S.card := Nat.pow_le_pow_left hQ _
  have hlog : 0 ≤ Real.logb 2 10 := Real.logb_nonneg (by norm_num) (by norm_num)
  have hlogUp : Real.logb 2 10 ≤ (10/3 : ℝ) := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 10^(3 : ℕ))
      (by norm_num : (10 : ℝ)^(3 : ℕ) ≤ 2^(10 : ℕ))
    simp only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one] at h
    norm_num at h
    linarith
  have hScardR : (2 : ℝ)*S.card ≤ (b : ℝ)+2 := by exact_mod_cast hScard
  have hScardR' : (S.card : ℝ) ≤ (b : ℝ)/2+1 := by linarith
  have hm := mul_le_mul_of_nonneg_left hScardR' hlog
  have hb := mul_le_mul_of_nonneg_right hlogUp (Nat.cast_nonneg (α := ℝ) b)
  have he : Real.logb 2 10*(S.card : ℝ) ≤ Real.logb 2 10+(5/3 : ℝ)*b := by nlinarith
  have hp : (10 : ℝ)^S.card = (2 : ℝ)^(Real.logb 2 10*(S.card : ℝ)) := by
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_logb (by norm_num) (by norm_num) (by norm_num),Real.rpow_natCast]
  calc
    _ ≤ (10 : ℝ)^S.card := by exact_mod_cast hn
    _ = _ := hp
    _ ≤ (2 : ℝ)^(Real.logb 2 10+(5/3 : ℝ)*b) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) he
    _ = _ := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]

end SymmetricSubgroupAsymptotics
