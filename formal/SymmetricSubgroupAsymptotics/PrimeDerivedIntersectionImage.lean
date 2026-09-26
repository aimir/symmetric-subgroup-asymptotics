import SymmetricSubgroupAsymptotics.PrimeDerivedJointHead
import SymmetricSubgroupAsymptotics.FiniteQuotientDerivedIntersection

/-! Exact cardinal correlations between an original normal subgroup,
its derived intersection and its actual evaluation image. The same N is
retained in every field; no stored normal profile or order is substituted. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] {G : Type*} [Group G] [Finite G]
variable (hker : (primeAbelianizationGroupMap p G).ker = commutator G)
variable (N : Subgroup G) [N.Normal]
include hker

theorem primeDerivedImage_pow_finrank_mul_intersection :
    p ^ Module.finrank (ZMod p) (primeDerivedImage p N) *
      Nat.card ↥(N ⊓ commutator G) = Nat.card N := by
  have h := normalChainQuotient_card_mul_inf (commutator G) N
  rw [derivedNormalImage_card p hker N,
    Module.natCard_eq_pow_finrank (K := ZMod p) (V := primeDerivedImage p N),
    Nat.card_zmod, inf_comm] at h
  exact h

theorem derivedIntersectionQuotient_card_eq_image :
    Nat.card (normalChainQuotient (N ⊓ commutator G) N) =
      Nat.card (primeDerivedImage p N) := by
  have h := normalChainQuotient_card_mul (N ⊓ commutator G) N inf_le_left
  have hi := primeDerivedImage_pow_finrank_mul_intersection p hker N
  have hc : Nat.card (primeDerivedImage p N) * Nat.card ↥(N ⊓ commutator G) = Nat.card N := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := primeDerivedImage p N), Nat.card_zmod]
    exact hi
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(N ⊓ commutator G))) (h.trans hc.symm)

theorem derivedIntersectionQuotient_log_card_eq_image :
    Nat.log p (Nat.card (normalChainQuotient (N ⊓ commutator G) N)) =
      Module.finrank (ZMod p) (primeDerivedImage p N) := by
  rw [derivedIntersectionQuotient_card_eq_image p hker N,
    Module.natCard_eq_pow_finrank (K := ZMod p) (V := primeDerivedImage p N),
    Nat.card_zmod, Nat.log_pow (Fact.out : p.Prime).one_lt]

theorem normal_card_le_pow_mul_derivedIntersection (a : ℕ)
    (ha : Module.finrank (ZMod p) (primeDerivedImage p N) ≤ a) :
    Nat.card N ≤ p ^ a * Nat.card ↥(N ⊓ commutator G) := by
  rw [← primeDerivedImage_pow_finrank_mul_intersection p hker N]
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (Fact.out : p.Prime).pos ha)

end SymmetricSubgroupAsymptotics
