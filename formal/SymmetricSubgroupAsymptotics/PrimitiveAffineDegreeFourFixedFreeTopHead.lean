import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourFixedFreeTranslationHead
import SymmetricSubgroupAsymptotics.RelativeSecondIsomorphism
import SymmetricSubgroupAsymptotics.RelativeAmbientTransport

/-! The fixed-free translation branch reduces each original relative
binary head to its actual normal image in the unchanged top quotient. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
local instance primitiveAffineDegreeFourFixedFreeTopHead_localFact1 : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem degreeFour_fixedFree_relative_head_le_actual_top_image
    (hp : P.p = 2) (g : preE7NonPairAction w U)
    (hg : (QuotientGroup.mk' (E block P) g) ^ 3 = 1)
    (hfixed : ∀ v : (elementaryChart block P).V,
      (elementaryChart block P).quotientRepresentation.ρ
        (QuotientGroup.mk' (E block P) g) v = v → v = 0)
    (N : Subgroup (preE7NonPairAction w U)) [N.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤
      Module.finrank (ZMod 2)
        (primeRelativeCharacters 2 (normalChainQuotient (E block P) N)) := by
  have hz := degreeFour_fixedFree_translation_intersection_head_zero
    block P hp g hg hfixed N
  have hz' : Module.finrank (ZMod 2)
      (primeRelativeCharacters 2 (N ⊓ E block P)) = 0 := by
    let e : preE7NonPairAction w U ≃* preE7NonPairAction w U := MulEquiv.refl _
    have he : (N ⊓ E block P).map e.toMonoidHom = E block P ⊓ N := by
      change (N ⊓ E block P).map (MonoidHom.id _) = E block P ⊓ N
      rw [Subgroup.map_id]
      exact inf_comm N (E block P)
    exact (relativeCharacterAmbientCongr 2 e (N ⊓ E block P)
      (E block P ⊓ N) he).finrank_eq.symm.trans hz
  have h := primeRelativeHead_chain_le (N ⊓ E block P) N 2 inf_le_left
  rw [hz', zero_add] at h
  exact h.trans_eq (primeRelativeHead_second_isomorphism 2 N (E block P))

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
