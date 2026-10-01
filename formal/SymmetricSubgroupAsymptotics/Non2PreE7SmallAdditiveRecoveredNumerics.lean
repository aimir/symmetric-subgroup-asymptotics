import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelNumerics
import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveS4
import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveA4W2

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

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
