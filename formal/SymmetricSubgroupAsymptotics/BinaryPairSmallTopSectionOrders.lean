import SymmetricSubgroupAsymptotics.BinaryPairNonelementarySectionBounds
import SymmetricSubgroupAsymptotics.PGroupRankPreservingKernelCommutator

/-! Exact original section orders and full abelianization transport.
These statements retain the actual top quotient and the same normal N. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G Q : Type} [Group G] [Group Q]

theorem abelianization_map_surjective_of_surjective
    (q : G →* Q) (hq : Function.Surjective q) :
    Function.Surjective (Abelianization.map q) := by
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (commutator Q) x
  obtain ⟨g, rfl⟩ := hq y
  exact ⟨Abelianization.of g, rfl⟩

theorem abelianization_exponent_of_surjective
    (q : G →* Q) (hq : Function.Surjective q) (p : ℕ)
    (hexp : ∀ a : Abelianization G, a ^ p = 1) :
    ∀ a : Abelianization Q, a ^ p = 1 := by
  intro a
  obtain ⟨b, rfl⟩ := abelianization_map_surjective_of_surjective q hq a
  rw [← map_pow, hexp, map_one]

namespace BinaryPairFrame
variable {X I : Type} [Finite X] [Finite I]
    {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)
    (N : Subgroup U) [N.Normal]

/-- Exact cardinality of the actual quotient extension. -/
theorem section_order_eq :
    Nat.card (U ⧸ N) =
      2 ^ Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N) *
        Nat.card (U ⧸ (F.top.ker ⊔ N)) := by
  have hA : Nat.card (F.zeroCutBase N).ker =
      2 ^ Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N) := by
    calc
      _ = Nat.card (F.kernelSpace ⧸ F.normalSpace N) :=
        (Nat.card_congr (F.sectionKernelEquiv N).symm.toEquiv).trans
          (Nat.card_congr Multiplicative.toAdd)
      _ = _ := by
        simpa only [Nat.card_zmod] using
          (Module.natCard_eq_pow_finrank (K := ZMod 2)
            (V := F.kernelSpace ⧸ F.normalSpace N))
  have hindex : (F.zeroCutBase N).ker.index = Nat.card (U ⧸ (F.top.ker ⊔ N)) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (F.zeroCutBase N)
      (F.zeroCutBase_surjective N)).toEquiv
  have htarget := (F.zeroCutBase N).ker.card_mul_index
  rw [hA, hindex] at htarget
  exact htarget.symm

theorem section_order_le_of_finrank_le (d t : ℕ)
    (hd : Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N) ≤ d)
    (ht : Nat.card F.top.range ≤ t) : Nat.card (U ⧸ N) ≤ 2 ^ d * t := by
  rw [F.section_order_eq N]
  exact Nat.mul_le_mul
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hd)
    ((Nat.card_le_card_of_surjective (F.sectionTopQuotient N)
      (F.sectionTopQuotient_surjective N)).trans ht)

/-- Every residual top abelianization is bounded by that of the SAME top. -/
theorem section_base_abelianization_card_le :
    Nat.card (Abelianization (U ⧸ (F.top.ker ⊔ N))) ≤
      Nat.card (Abelianization F.top.range) :=
  Nat.card_le_card_of_surjective (Abelianization.map (F.sectionTopQuotient N))
    (abelianization_map_surjective_of_surjective _ (F.sectionTopQuotient_surjective N))

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
