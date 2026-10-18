import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralAbelianSupplement
import SymmetricSubgroupAsymptotics.PrimeCharacterSubgroupCapacity

/-! The full-image branch uses the order of the actual abelianization.
No extension of F_p-valued characters from a subgroup is asserted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural

variable {G : Type} [Group G] [Finite G]

/-- Every full-image relative head fits in the actual abelianization's
order budget. This retains its literal radical and does not replace the
resulting abelian quotient by a guessed exponent-p quotient. -/
theorem relativeHead_pow_le_abelianization_card
    (p : ℕ) [Fact p.Prime] (K M : Subgroup G) [M.Normal]
    (hKM : K ⊔ M = ⊤) (hK : IsMulCommutative K) :
    p ^ Module.finrank (ZMod p) (primeRelativeCharacters p M) ≤
      Nat.card (G ⧸ commutator G) := by
  let R := primeRelativeRadical p M
  have hcomm : IsMulCommutative (G ⧸ R) :=
    relativeRadicalQuotient_commutative p K M hKM hK
  have hder : commutator G ≤ R :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcomm
  let f : (G ⧸ commutator G) →* (G ⧸ R) :=
    QuotientGroup.lift (commutator G) (QuotientGroup.mk' R) (by
      rw [QuotientGroup.ker_mk']; exact hder)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective R q
    exact ⟨QuotientGroup.mk' (commutator G) g,rfl⟩
  have hquot : Nat.card (G ⧸ R) ≤ Nat.card (G ⧸ commutator G) :=
    Nat.card_le_card_of_surjective f hf
  rw [primeRelativeHead_radical_image_eq p M]
  calc
    _ ≤ p ^ Module.finrank (ZMod p)
        (PrimeCharacters p (normalChainQuotient R M)) :=
      Nat.pow_le_pow_right (Fact.out : p.Prime).pos (Submodule.finrank_le _)
    _ ≤ Nat.card (normalChainQuotient R M) := primeCharacters_pow_finrank_le_card p _
    _ ≤ Nat.card (G ⧸ R) :=
      Nat.card_le_card_of_injective (normalChainQuotient R M).subtype Subtype.val_injective
    _ ≤ Nat.card (G ⧸ commutator G) := hquot

end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural
