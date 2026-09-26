import SymmetricSubgroupAsymptotics.BinaryPGroupExteriorComparison
import SymmetricSubgroupAsymptotics.BinaryCyclicFourCount
import SymmetricSubgroupAsymptotics.BinaryCyclicFourCountNumerics

/-! An explicit Hall-mixture bound for actual C4^a × C2^R × B subgroups.
Only B is replaced by an elementary abelian comparison group. The original
C4 coordinates are retained, and their square obstruction is counted by
the proved two-column formula. There is no extra u²/4 term.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCyclicFourMixedHall

open BinaryCyclicFourSquareObstruction

private def binaryPairChart (R u : ℕ) :
    ((Fin R → ZMod 2) × (Fin u → ZMod 2)) ≃ₗ[ZMod 2] (Fin (R+u) → ZMod 2) :=
  LinearEquiv.ofFinrankEq _ _ (by
    simp only [Module.finrank_prod,Module.finrank_pi,Fintype.card_fin])

private def binaryPairEquiv (R u : ℕ) :
    (Multiplicative (Fin R → ZMod 2) × Multiplicative (Fin u → ZMod 2)) ≃*
      Multiplicative (Fin (R+u) → ZMod 2) :=
  ((MulEquiv.prodMultiplicative (G := Fin R → ZMod 2)
    (H := Fin u → ZMod 2)).symm).trans (binaryPairChart R u).toAddEquiv.toMultiplicative

/-- Reassociate only the elementary binary factors, retaining C4 literally. -/
def regroup (R a u : ℕ) :
    (Original R a × BinaryPGroupExteriorComparison.Binary u) ≃* Original (R+u) a :=
  (MulEquiv.prodAssoc :
    ((Multiplicative (Fin a → ZMod 4) × Multiplicative (Fin R → ZMod 2)) ×
        Multiplicative (Fin u → ZMod 2)) ≃*
      (Multiplicative (Fin a → ZMod 4) ×
        (Multiplicative (Fin R → ZMod 2) × Multiplicative (Fin u → ZMod 2)))).trans
    ((MulEquiv.refl (Multiplicative (Fin a → ZMod 4))).prodCongr (binaryPairEquiv R u))

theorem regroup_cyclicFour (R a u : ℕ)
    (x : Original R a × BinaryPGroupExteriorComparison.Binary u) :
    (regroup R a u x).1 = x.1.1 := rfl

theorem abelian_subgroup_card_le (R a : ℕ) :
    (Nat.card (Subgroup (Original R a)) : ℝ) ≤
      (a+1 : ℝ) * (R+a+1 : ℝ) * (eulerProduct⁻¹)^2 *
        (2 : ℝ)^(((a : ℝ)^2+((R : ℝ)+a)^2)/4) := by
  have hcount : (Nat.card (Subgroup (Original R a)) : ℝ) =
      (cyclicFourGaussianSum R a : ℝ) := by
    unfold cyclicFourGaussianSum
    push_cast
    exact BinaryCyclicFourCount.card_eq_two_column_sum R a
  rw [hcount]
  exact cyclicFourGaussianSum_le R a

/-- Uniform bound for every actual finite B of order 2^u. No subgroup-count
premise is supplied, and the entire original C4 factor remains present. -/
theorem mixed_subgroup_card_le (R a : ℕ) (B : Type*) [Group B] [Finite B]
    (u : ℕ) (hB : Nat.card B = 2^u) :
    (Nat.card (Subgroup (Original R a × B)) : ℝ) ≤
      (a+1 : ℝ) * (R+u+a+1 : ℝ) * (eulerProduct⁻¹)^2 *
        (2 : ℝ)^(((a : ℝ)^2+((R : ℝ)+u+a)^2)/4) := by
  have hc : Nat.card (Subgroup (Original R a × B)) ≤
      Nat.card (Subgroup (Original (R+u) a)) :=
    (BinaryPGroupExteriorComparison.subgroup_card_le (Original R a) B u hB).trans_eq
      (Nat.card_congr (regroup R a u).mapSubgroup.toEquiv)
  have hcR : (Nat.card (Subgroup (Original R a × B)) : ℝ) ≤
      (Nat.card (Subgroup (Original (R+u) a)) : ℝ) := by exact_mod_cast hc
  simpa only [Nat.cast_add] using hcR.trans (abelian_subgroup_card_le (R+u) a)

local instance subgroupFinite {G : Type*} [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

/-- An arbitrary original survival family is a literal subfamily of the
counted group. No naturality or transported survival predicate is assumed. -/
theorem mixed_subfamily_card_le (R a : ℕ) (B : Type*) [Group B] [Finite B]
    (u : ℕ) (hB : Nat.card B = 2^u) (P : Subgroup (Original R a × B) → Prop) :
    (Nat.card {H : Subgroup (Original R a × B) // P H} : ℝ) ≤
      (a+1 : ℝ) * (R+u+a+1 : ℝ) * (eulerProduct⁻¹)^2 *
        (2 : ℝ)^(((a : ℝ)^2+((R : ℝ)+u+a)^2)/4) := by
  have h : Nat.card {H : Subgroup (Original R a × B) // P H} ≤
      Nat.card (Subgroup (Original R a × B)) :=
    Nat.card_le_card_of_injective
      (Subtype.val : {H : Subgroup (Original R a × B) // P H} →
        Subgroup (Original R a × B)) Subtype.val_injective
  have hR : (Nat.card {H : Subgroup (Original R a × B) // P H} : ℝ) ≤
      (Nat.card (Subgroup (Original R a × B)) : ℝ) := by exact_mod_cast h
  exact hR.trans (mixed_subgroup_card_le R a B u hB)

end SymmetricSubgroupAsymptotics.BinaryCyclicFourMixedHall
