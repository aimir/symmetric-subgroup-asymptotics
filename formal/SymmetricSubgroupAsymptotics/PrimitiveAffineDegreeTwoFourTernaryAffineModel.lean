import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourTernaryStructure
import SymmetricSubgroupAsymptotics.SemidirectAbelianCentralizerTransport

/-! A single assembler for the eight literal ternary affine models.
Every input concerns the compact translation/complement model or its
displayed action on twelve points; the original core and quotient are
constructed through the actual group equivalence. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

open SemidirectProduct SemidirectAbelianCentralizer

variable {V H : Type} [CommGroup V] [Group H]
variable {φ : H →* MulAut V}

/-- Install an exact affine realization of the original permutation group.
The centralizer condition is checked only on the complement action kernel. -/
noncomputable def degreeTwoFourTernaryTopStructureOfAffine
    (D : DegreeTwoPairTopFiniteInterface 12)
    (e : D.top ≃* V ⋊[φ] H)
    (hV : ∀ v : V, v ^ (3 : ℕ) = 1)
    (hcard : 9 ≤ Nat.card V)
    (hH : IsPGroup 2 H)
    (hker : Nat.card φ.ker ≤ 2)
    (htrans : MulAction.IsPretransitive D.top (Fin 12))
    (horbits : ∀ x y : Fin 12,
      degreeTwoFourTernaryBlock x = degreeTwoFourTernaryBlock y ↔
        ∃ v : V, (e.symm (inl v) : Equiv.Perm (Fin 12)) x = y) :
    DegreeTwoFourTernaryTopStructure D where
  core := (originalProjection e).ker
  core_normal := inferInstance
  core_commutative := originalTranslation_commutative e
  core_exponent_three := originalTranslation_exponent e 3 hV
  core_card_lower := by rw [originalTranslation_card]; exact hcard
  top_transitive := htrans
  same_block_iff_core_orbit := by
    intro x y
    rw [horbits]
    constructor
    · rintro ⟨v, hv⟩
      exact ⟨originalTranslation e v, hv⟩
    · rintro ⟨c, hc⟩
      obtain ⟨v, rfl⟩ := (originalTranslationEquiv e).surjective c
      exact ⟨v, hc⟩
  quotient_binary := by
    exact hH.of_equiv (QuotientGroup.quotientKerEquivOfSurjective
      (originalProjection e) (originalProjection_surjective e)).symm
  core_centralizer_quotient_card_le_two := by
    rw [original_centralizer_quotient_card]
    exact hker

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
