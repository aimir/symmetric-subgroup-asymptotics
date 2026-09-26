import SymmetricSubgroupAsymptotics.PrimeAbelianization
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card

/-! Character dimensions and a subgroup annihilated by the same characters
share one original group-order budget. Evaluation on the retained character
space is onto; its actual kernel contains the displayed subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]

/-- The complete prime character quotient cannot exceed its original group. -/
theorem primeCharacters_pow_finrank_le_card (G : Type*) [Group G] [Finite G] :
    p ^ Module.finrank (ZMod p) (PrimeCharacters p G) ≤ Nat.card G := by
  have h := Nat.card_le_card_of_surjective (primeAbelianizationGroupMap p G)
    (primeAbelianizationGroupMap_surjective p G)
  change Nat.card (PrimeAbelianization p G) ≤ Nat.card G at h
  rw [Module.natCard_eq_pow_finrank (K := ZMod p)
    (V := PrimeAbelianization p G)] at h
  simpa only [Nat.card_zmod, Subspace.dual_finrank_eq] using h

variable {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

/-- Evaluation on precisely the retained characters, with the original G. -/
def retainedCharacterEvaluation (χ : V →ₗ[ZMod p] PrimeCharacters p G) :
    G →* Multiplicative (Module.Dual (ZMod p) V) where
  toFun g := Multiplicative.ofAdd
    (χ.dualMap (primeAbelianizationMap p G (Additive.ofMul g)))
  map_one' := by
    change χ.dualMap (primeAbelianizationMap p G 0) = 0
    rw [map_zero, map_zero]
  map_mul' g h := by
    change χ.dualMap (primeAbelianizationMap p G
      (Additive.ofMul g + Additive.ofMul h)) = _
    rw [map_add, map_add]
    rfl

theorem retainedCharacterEvaluation_surjective [Finite G]
    (χ : V →ₗ[ZMod p] PrimeCharacters p G) (hχ : Function.Injective χ) :
    Function.Surjective (retainedCharacterEvaluation p χ) :=
  (LinearMap.dualMap_surjective_of_injective hχ).comp
    (primeAbelianizationMap_surjective p G)

/-- An injected subgroup annihilated by all retained characters shares
the original cardinal budget with their dimension. Normality is unnecessary. -/
theorem retainedCharacters_subgroup_card_bound [Finite G] [Finite V]
    {L : Type*} [Group L] [Finite L]
    (χ : V →ₗ[ZMod p] PrimeCharacters p G) (hχ : Function.Injective χ)
    (φ : L →* G) (hφ : Function.Injective φ)
    (hzero : ∀ v l, χ v (Additive.ofMul (φ l)) = 0) :
    p ^ Module.finrank (ZMod p) V * Nat.card L ≤ Nat.card G := by
  let f := retainedCharacterEvaluation p χ
  have hf := retainedCharacterEvaluation_surjective p χ hχ
  let j : L → f.ker := fun l => ⟨φ l, by
    change χ.dualMap (primeAbelianizationMap p G (Additive.ofMul (φ l))) = 0
    ext v
    exact hzero v l⟩
  have hj : Function.Injective j := fun _ _ h => hφ (congrArg Subtype.val h)
  have hcard : Nat.card L ≤ Nat.card f.ker := Nat.card_le_card_of_injective j hj
  have hquot : Nat.card (G ⧸ f.ker) = p ^ Module.finrank (ZMod p) V := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
    change Nat.card (Module.Dual (ZMod p) V) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod p)
      (V := Module.Dual (ZMod p) V), Subspace.dual_finrank_eq, Nat.card_zmod]
  calc
    _ ≤ p ^ Module.finrank (ZMod p) V * Nat.card f.ker := Nat.mul_le_mul_left _ hcard
    _ = Nat.card G := by
      rw [← hquot]
      exact (Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker).symm

/-- The retained rank and the entire subgroup character rank consume the
same order budget. This is the coupled inequality, not two separate bounds. -/
theorem retainedCharacters_subgroup_rank_bound [Finite G] [Finite V]
    {L : Type*} [Group L] [Finite L]
    (χ : V →ₗ[ZMod p] PrimeCharacters p G) (hχ : Function.Injective χ)
    (φ : L →* G) (hφ : Function.Injective φ)
    (hzero : ∀ v l, χ v (Additive.ofMul (φ l)) = 0) :
    p ^ (Module.finrank (ZMod p) V +
      Module.finrank (ZMod p) (PrimeCharacters p L)) ≤ Nat.card G := by
  rw [pow_add]
  exact (Nat.mul_le_mul_left _ (primeCharacters_pow_finrank_le_card p L)).trans
    (retainedCharacters_subgroup_card_bound p χ hχ φ hφ hzero)

end SymmetricSubgroupAsymptotics
