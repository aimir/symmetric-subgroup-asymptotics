import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelNumerics
import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveS4

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

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
