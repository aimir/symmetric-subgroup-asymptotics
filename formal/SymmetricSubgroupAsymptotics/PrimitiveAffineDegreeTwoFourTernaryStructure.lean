import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopInterface

/-! # Structural interface for the four-ternary degree-twelve tops -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- Common block label on the original twelve points. -/
def degreeTwoFourTernaryBlock (x : Fin 12) : Fin 4 :=
  ⟨x.val % 4, Nat.mod_lt _ (by norm_num)⟩

/-- Minimal structural input used by the common compression proof. -/
structure DegreeTwoFourTernaryTopStructure
    (D : DegreeTwoPairTopFiniteInterface 12) : Type 1 where
  core : Subgroup D.top
  core_normal : core.Normal
  core_commutative : IsMulCommutative core
  core_exponent_three : ∀ c : core, c ^ (3 : ℕ) = 1
  core_card_lower : 9 ≤ Nat.card core
  top_transitive : MulAction.IsPretransitive D.top (Fin 12)
  same_block_iff_core_orbit : ∀ x y : Fin 12,
    degreeTwoFourTernaryBlock x = degreeTwoFourTernaryBlock y ↔
      ∃ c : core, c.1.1 x = y
  quotient_binary :
    letI : core.Normal := core_normal
    IsPGroup 2 (D.top ⧸ core)
  core_centralizer_quotient_card_le_two :
    letI : core.Normal := core_normal
    Nat.card ((Subgroup.centralizer (core : Set D.top)).map
      (QuotientGroup.mk' core)) ≤ 2

namespace DegreeTwoFourTernaryTopStructure

variable {D : DegreeTwoPairTopFiniteInterface 12}
  (S : DegreeTwoFourTernaryTopStructure D)

/-- A normal subgroup disjoint from the ternary core centralizes the core. -/
theorem normal_disjoint_core_card_le_two
    (L : Subgroup D.top) [L.Normal]
    (hdisjoint : L ⊓ S.core = ⊥) :
    Nat.card L ≤ 2 := by
  letI : S.core.Normal := S.core_normal
  have hcomm : ⁅L, S.core⁆ = ⊥ := by
    apply le_antisymm
    · exact (Subgroup.commutator_le_inf (H₁ := L) (H₂ := S.core)).trans_eq
        hdisjoint
    · exact bot_le
  have hcentral : L ≤ Subgroup.centralizer (S.core : Set D.top) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  let q := QuotientGroup.mk' S.core
  let f : L →* D.top ⧸ S.core := q.comp L.subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply Subtype.ext
    change QuotientGroup.mk' S.core (x : D.top) = 1 at hx
    have hxcore : (x : D.top) ∈ S.core :=
      (QuotientGroup.eq_one_iff (x : D.top)).mp hx
    have hxbot : (x : D.top) ∈ (⊥ : Subgroup D.top) := by
      rw [← hdisjoint]
      exact ⟨x.property, hxcore⟩
    exact Subgroup.mem_bot.mp hxbot
  let intoCentralizerQuotient : L →
      (Subgroup.centralizer (S.core : Set D.top)).map q := fun x ↦
    ⟨f x, ⟨(x : D.top), hcentral x.property, rfl⟩⟩
  have hinjective : Function.Injective intoCentralizerQuotient := by
    intro x y hxy
    apply hf
    exact congrArg Subtype.val hxy
  exact (Nat.card_le_card_of_injective intoCentralizerQuotient hinjective).trans
    S.core_centralizer_quotient_card_le_two

theorem normal_binary_disjoint_card_le_two
    (L : Subgroup D.top) [L.Normal]
    (_ : IsPGroup 2 L) (hdisjoint : L ⊓ S.core = ⊥) :
    Nat.card L ≤ 2 :=
  S.normal_disjoint_core_card_le_two L hdisjoint

end DegreeTwoFourTernaryTopStructure
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
