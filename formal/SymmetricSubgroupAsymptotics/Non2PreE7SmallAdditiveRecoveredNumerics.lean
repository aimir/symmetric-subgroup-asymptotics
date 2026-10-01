import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelNumerics
import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveS4
import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveA4W2
import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveLin
import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveTF

/-!
# Numerical completion of the recovered small additive owners

This file attaches the finite coefficient totals to the concrete S4, A4W2,
LIN and TF predicates.  The group theory and local epimorphism estimates live
in their respective source files; only finite cardinalities and the common
menu-mass envelope are used here.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

private theorem s4_aut_tail_le :
    (2 : ℝ) * Nat.card (Equiv.Perm (Fin 4) ≃* Equiv.Perm (Fin 4)) ≤
      (2 : ℝ) ^ (144 : ℝ) := by
  let G := Equiv.Perm (Fin 4)
  have h : Nat.card (G ≃* G) ≤ 24 ^ 24 := by
    have hraw := mulEquiv_card_le_card_pow_card G
    calc
      Nat.card (G ≃* G) ≤ Nat.card G ^ Nat.card G := hraw
      _ = 24 ^ 24 := by
        congr 1 <;> rw [Nat.card_perm, Nat.card_fin] <;> norm_num
  have hnat : 2 * Nat.card (Equiv.Perm (Fin 4) ≃* Equiv.Perm (Fin 4)) ≤ 2 ^ 144 :=
    (Nat.mul_le_mul_left 2 h).trans (by norm_num)
  exact_mod_cast hnat

/-- The natural S4 predicate, now with both numerical totals required by T1. -/
noncomputable def preE7_s4_numericalData (w : ℕ)
    (i : PreE7NonPairActionClass w) (S : PreE7S4Source w i) :
    PreE7SmallAdditiveNumericalData .s4 w i := by
  obtain ⟨rfl, h⟩ := S
  let M := s4Model i h
  apply M.numericalData .s4
  · intro b
    calc
      (Nat.card {N : Subgroup (preE7NonPairAction 4 i) // N.Normal} : ℝ) ≤
          (2 : ℝ) ^ (Nat.card M.G : ℝ) := M.normalAxis_card_cast_le_modelRpow
      _ = (2 : ℝ) ^ (24 : ℝ) := by
        have hcard : Nat.card M.G = 24 := by
          change Nat.card (Equiv.Perm (Fin 4)) = 24
          rw [Nat.card_perm, Nat.card_fin]
          norm_num
        congr 1
        exact_mod_cast hcard
      _ ≤ (2 : ℝ) ^ (16 * (4 : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        norm_num
      _ ≤ _ := two_rpow_sixteen_width_le_menuMass (w := 4) (by norm_num) b
  · intro b
    change (2 : ℝ) * Nat.card (Equiv.Perm (Fin 4) ≃* Equiv.Perm (Fin 4)) ≤ _
    calc
      _ ≤ (2 : ℝ) ^ (144 : ℝ) := s4_aut_tail_le
      _ ≤ _ := by
        convert two_rpow_thirtySix_width_le_menuMass (w := 4) (by norm_num) b using 1 <;>
          norm_num

private theorem a4_card : Nat.card NaturalS4.a4 = 12 := by
  rw [show Nat.card NaturalS4.a4 =
      Nat.card {s : Equiv.Perm (Fin 4) // s ∈ NaturalS4.a4Set} from rfl,
    Nat.card_eq_finsetCard]
  decide

private theorem a4w2_card : Nat.card A4WreathC2.G = 288 := by
  rw [SemidirectProduct.card, Nat.card_prod, a4_card]
  norm_num

private theorem a4w2_aut_tail_le :
    (Nat.card (A4WreathC2.G ≃* A4WreathC2.G) : ℝ) ≤
      (2 : ℝ) ^ (512 : ℝ) := by
  have h := mulEquiv_card_le_card_pow_log A4WreathC2.G
  rw [a4w2_card] at h
  norm_num at h
  have hnat : Nat.card (A4WreathC2.G ≃* A4WreathC2.G) ≤ 2 ^ 512 :=
    h.trans (by
      calc
        288 ^ 8 ≤ 512 ^ 8 := pow_le_pow_left' (by norm_num) _
        _ = 2 ^ 72 := by norm_num
        _ ≤ 2 ^ 512 := Nat.pow_le_pow_right (by norm_num) (by norm_num))
  exact_mod_cast hnat

/-- The natural A4-wreath-C2 predicate with its complete numerical totals. -/
noncomputable def preE7_a4w2_numericalData (w : ℕ)
    (i : PreE7NonPairActionClass w) (S : PreE7A4W2Source w i) :
    PreE7SmallAdditiveNumericalData .a4w2 w i := by
  let e := S.chart
  have h := S.action_eq
  have hw : w = 8 := by
    rw [width_eq_of_relabel e]
    simp
  subst w
  let M := a4w2Model i e h
  apply M.numericalData .a4w2
  · intro b
    calc
      (Nat.card {N : Subgroup (preE7NonPairAction 8 i) // N.Normal} : ℝ) ≤
          (2 : ℝ) ^ (Nat.card M.G : ℝ) := M.normalAxis_card_cast_le_modelRpow
      _ = (2 : ℝ) ^ (288 : ℝ) := by
        congr 1
        exact_mod_cast a4w2_card
      _ ≤ (2 : ℝ) ^ (64 * (8 : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        norm_num
      _ ≤ _ := two_rpow_sixtyFour_width_le_menuMass (w := 8) (by norm_num) b
  · intro b
    change (Nat.card (A4WreathC2.G ≃* A4WreathC2.G) : ℝ) ≤ _
    calc
      _ ≤ (2 : ℝ) ^ (512 : ℝ) := a4w2_aut_tail_le
      _ ≤ _ := by
        convert two_rpow_sixtyFour_width_le_menuMass (w := 8) (by norm_num) b using 1 <;>
          norm_num

private def gl3MatrixEquiv : LinearThree.GL3 ≃
    {A : LinearThree.M2 // A ∈ LinearThree.glSet} where
  toFun g := ⟨g, LinearThree.coe_mem_glSet g⟩
  invFun A := LinearThree.ofGL A.1 A.2
  left_inv g := Units.ext rfl
  right_inv A := Subtype.ext rfl

private theorem gl3_card : Nat.card LinearThree.GL3 = 48 := by
  rw [Nat.card_congr gl3MatrixEquiv, Nat.card_eq_finsetCard]
  decide

private def sl3MatrixEquiv : LinearThree.SL3 ≃
    {A : LinearThree.M2 // A ∈ LinearThree.slSet} where
  toFun g := ⟨g.1, (LinearThree.mem_slSub g.1).mp g.2⟩
  invFun A := ⟨LinearThree.ofGL A.1 (LinearThree.slSet_sub A.1 A.2),
    (LinearThree.mem_slSub _).mpr A.2⟩
  left_inv g := Subtype.ext (Units.ext rfl)
  right_inv A := Subtype.ext rfl

private theorem sl3_card : Nat.card LinearThree.SL3 = 24 := by
  rw [Nat.card_congr sl3MatrixEquiv, Nat.card_eq_finsetCard]
  decide

/-- Both actual LIN modes with their complete numerical totals. -/
noncomputable def preE7_lin_numericalData (w : ℕ)
    (i : PreE7NonPairActionClass w) (S : PreE7LinSource w i) :
    PreE7SmallAdditiveNumericalData .lin w i := by
  cases S with
  | gl e h =>
      have hw := lin_width e
      subst w
      let M := linGLModel i e h
      apply M.numericalData .lin
      · intro b
        calc
          (Nat.card {N : Subgroup (preE7NonPairAction 8 i) // N.Normal} : ℝ) ≤
              (2 : ℝ) ^ (Nat.card M.G : ℝ) := M.normalAxis_card_cast_le_modelRpow
          _ = (2 : ℝ) ^ (48 : ℝ) := by
            congr 1
            exact_mod_cast gl3_card
          _ ≤ (2 : ℝ) ^ (64 * (8 : ℝ)) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            norm_num
          _ ≤ _ := two_rpow_sixtyFour_width_le_menuMass (w := 8) (by norm_num) b
      · intro b
        change (2 : ℝ) * Nat.card (Equiv.Perm (Fin 4) ≃* Equiv.Perm (Fin 4)) ≤ _
        calc
          _ ≤ (2 : ℝ) ^ (144 : ℝ) := s4_aut_tail_le
          _ ≤ (2 : ℝ) ^ (64 * (8 : ℝ)) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            norm_num
          _ ≤ _ := two_rpow_sixtyFour_width_le_menuMass (w := 8) (by norm_num) b
  | sl e h =>
      have hw := lin_width e
      subst w
      let M := linSLModel i e h
      apply M.numericalData .lin
      · intro b
        have haxis := M.normalAxis_card_cast_le_modelRpow
        rw [show Nat.card M.G = 24 by exact sl3_card] at haxis
        calc
          _ ≤ (2 : ℝ) ^ (24 : ℝ) + 1 := by
            rw [show M.mainConstant = 1 by rfl]
            simpa only [add_comm] using add_le_add_right haxis 1
          _ ≤ (2 : ℝ) ^ (25 : ℝ) := by norm_num
          _ ≤ (2 : ℝ) ^ (64 * (8 : ℝ)) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            norm_num
          _ ≤ _ := two_rpow_sixtyFour_width_le_menuMass (w := 8) (by norm_num) b
      · intro b
        change (0 : ℝ) ≤ _
        positivity

private def xsPairBlockEquiv : TwoFourDiagonal.Xs ≃
    {p : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) // p ∈ TwoFourDiagonal.xsPairs} ×
      Multiplicative (ZMod 2) where
  toFun x := (⟨(x : TwoFourDiagonal.W4).left, TwoFourDiagonal.mem_xsPairs x.2⟩,
    (x : TwoFourDiagonal.W4).right)
  invFun y := ⟨SemidirectProduct.inl y.1.1 * SemidirectProduct.inr y.2,
    TwoFourDiagonal.mem_Xs_of_pair y.1.2 y.2⟩
  left_inv x := Subtype.ext (SemidirectProduct.inl_left_mul_inr_right
    (x : TwoFourDiagonal.W4))
  right_inv y := by
    apply Prod.ext
    · apply Subtype.ext
      show (SemidirectProduct.inl y.1.1 * SemidirectProduct.inr y.2 :
        TwoFourDiagonal.W4).left = y.1.1
      simp
    · show (SemidirectProduct.inl y.1.1 * SemidirectProduct.inr y.2 :
        TwoFourDiagonal.W4).right = y.2
      simp

private theorem xsPairs_card : TwoFourDiagonal.xsPairs.card = 96 := by
  native_decide

private theorem xs_card : Nat.card TwoFourDiagonal.Xs = 192 := by
  rw [Nat.card_congr xsPairBlockEquiv, Nat.card_prod, Nat.card_eq_fintype_card]
  simp [xsPairs_card]

private theorem xc_card_le : Nat.card TwoFourDiagonal.Xc ≤ 192 := by
  calc
    Nat.card TwoFourDiagonal.Xc ≤ Nat.card TwoFourDiagonal.Xs :=
      Nat.card_le_card_of_injective (Subgroup.inclusion TwoFourDiagonal.Xc_le_Xs)
        (Subgroup.inclusion_injective _)
    _ = 192 := xs_card

private theorem xg_card_le : Nat.card TwoFourDiagonal.Xg ≤ 192 := by
  calc
    Nat.card TwoFourDiagonal.Xg ≤ Nat.card TwoFourDiagonal.Xs :=
      Nat.card_le_card_of_injective (Subgroup.inclusion TwoFourDiagonal.Xg_le_Xs)
        (Subgroup.inclusion_injective _)
    _ = 192 := xs_card

private theorem tf_aut_tail_le (G : Type*) [Group G] [Finite G]
    (hcard : Nat.card G ≤ 192) :
    (Nat.card (G ≃* G) : ℝ) ≤ (2 : ℝ) ^ (512 : ℝ) := by
  have hlog : Nat.log 2 (Nat.card G) ≤ 7 :=
    (Nat.log_mono_right hcard).trans (by norm_num)
  have hnat : Nat.card (G ≃* G) ≤ 2 ^ 512 :=
    (mulEquiv_card_le_card_pow_log G).trans <| calc
      Nat.card G ^ Nat.log 2 (Nat.card G) ≤ 192 ^ Nat.log 2 (Nat.card G) :=
        Nat.pow_le_pow_left hcard _
      _ ≤ 192 ^ 7 := Nat.pow_le_pow_right (by norm_num) hlog
      _ ≤ 2 ^ 64 := by norm_num
      _ ≤ 2 ^ 512 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  exact_mod_cast hnat

/-- The three actual TF modes with their complete numerical totals. -/
noncomputable def preE7_tf_numericalData (w : ℕ)
    (i : PreE7NonPairActionClass w) (S : PreE7TFSource w i) :
    PreE7SmallAdditiveNumericalData .tf w i := by
  cases S with
  | xc e h =>
      have hw := tf_width e
      subst w
      let M := tfXcModel i e h
      apply M.numericalData .tf
      · intro b
        calc
          (Nat.card {N : Subgroup (preE7NonPairAction 8 i) // N.Normal} : ℝ) ≤
              (2 : ℝ) ^ (Nat.card M.G : ℝ) := M.normalAxis_card_cast_le_modelRpow
          _ ≤ (2 : ℝ) ^ (192 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            exact_mod_cast xc_card_le
          _ ≤ (2 : ℝ) ^ (64 * (8 : ℝ)) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            norm_num
          _ ≤ _ := two_rpow_sixtyFour_width_le_menuMass (w := 8) (by norm_num) b
      · intro b
        change (Nat.card (TwoFourDiagonal.Xc ≃* TwoFourDiagonal.Xc) : ℝ) ≤ _
        calc
          _ ≤ (2 : ℝ) ^ (512 : ℝ) := tf_aut_tail_le _ xc_card_le
          _ ≤ _ := by
            convert two_rpow_sixtyFour_width_le_menuMass (w := 8) (by norm_num) b using 1 <;>
              norm_num
  | xg e h =>
      have hw := tf_width e
      subst w
      let M := tfXgModel i e h
      apply M.numericalData .tf
      · intro b
        calc
          (Nat.card {N : Subgroup (preE7NonPairAction 8 i) // N.Normal} : ℝ) ≤
              (2 : ℝ) ^ (Nat.card M.G : ℝ) := M.normalAxis_card_cast_le_modelRpow
          _ ≤ (2 : ℝ) ^ (192 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            exact_mod_cast xg_card_le
          _ ≤ (2 : ℝ) ^ (64 * (8 : ℝ)) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            norm_num
          _ ≤ _ := two_rpow_sixtyFour_width_le_menuMass (w := 8) (by norm_num) b
      · intro b
        change (Nat.card (TwoFourDiagonal.Xg ≃* TwoFourDiagonal.Xg) : ℝ) ≤ _
        calc
          _ ≤ (2 : ℝ) ^ (512 : ℝ) := tf_aut_tail_le _ xg_card_le
          _ ≤ _ := by
            convert two_rpow_sixtyFour_width_le_menuMass (w := 8) (by norm_num) b using 1 <;>
              norm_num
  | xs e h =>
      have hw := tf_width e
      subst w
      let M := tfXsModel i e h
      apply M.numericalData .tf
      · intro b
        calc
          (Nat.card {N : Subgroup (preE7NonPairAction 8 i) // N.Normal} : ℝ) ≤
              (2 : ℝ) ^ (Nat.card M.G : ℝ) := M.normalAxis_card_cast_le_modelRpow
          _ = (2 : ℝ) ^ (192 : ℝ) := by congr 1; exact_mod_cast xs_card
          _ ≤ (2 : ℝ) ^ (64 * (8 : ℝ)) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            norm_num
          _ ≤ _ := two_rpow_sixtyFour_width_le_menuMass (w := 8) (by norm_num) b
      · intro b
        change (Nat.card (TwoFourDiagonal.Xs ≃* TwoFourDiagonal.Xs) : ℝ) ≤ _
        calc
          _ ≤ (2 : ℝ) ^ (512 : ℝ) := tf_aut_tail_le _ (by rw [xs_card])
          _ ≤ _ := by
            convert two_rpow_sixtyFour_width_le_menuMass (w := 8) (by norm_num) b using 1 <;>
              norm_num

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
