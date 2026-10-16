import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourOriginalTranslationCoordinates
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreNonbinarySocle
import SymmetricSubgroupAsymptotics.BinaryFourSymmetricKleinNormalCover

/-! The preimage of the actual canonical Klein subgroup is a normal
binary subgroup of the original U, even for an unsplit extension. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

namespace BinaryFourCanonicalBinaryCores

open BinaryFourBlockAugmentation BinaryFourSymmetricBlockActions SemidirectProduct

theorem a4_klein_isPGroup : IsPGroup 2 BinaryKleinTernaryNormalChain.kleinKernel := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  change x.1 ^ 2 = 1
  have hxright : x.1.right = 1 := x.2
  have hxform : (inl x.1.left : Complement) = x.1 :=
    SemidirectProduct.ext rfl hxright.symm
  have hp : ∀ p : Klein, p ^ 2 = 1 := by decide +kernel
  rw [← hxform, ← map_pow, hp, map_one]

theorem s4_klein_isPGroup : IsPGroup 2 BinaryFourSymmetricKleinNormalCover.klein := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  change x.1 ^ 2 = 1
  obtain ⟨ht, hb⟩ := (BinaryFourSymmetricKleinNormalCover.mem_klein x.1).mp x.2
  have heven : (inl x.1.left.left : Complement) = x.1.left :=
    SemidirectProduct.ext rfl ht.symm
  have hxform : (inl (inl x.1.left.left : Complement) : SymmetricComplement) = x.1 := by
    apply SemidirectProduct.ext
    · exact heven
    · exact hb.symm
  have hp : ∀ p : Klein, p ^ 2 = 1 := by decide +kernel
  rw [← hxform, ← map_pow, ← map_pow, hp, map_one, map_one]

end BinaryFourCanonicalBinaryCores

namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]

def originalCanonicalKleinCore {G : Type} [Group G]
    (eG : DegreeFourComplementQuotient block P ≃* G) (K : Subgroup G) :
    Subgroup (preE7NonPairAction w U) :=
  (K.comap eG.toMonoidHom).comap (QuotientGroup.mk' (E block P))

instance originalCanonicalKleinCore_normal {G : Type} [Group G]
    (eG : DegreeFourComplementQuotient block P ≃* G) (K : Subgroup G) [K.Normal] :
    (originalCanonicalKleinCore block P eG K).Normal := by
  unfold originalCanonicalKleinCore
  infer_instance

theorem originalCanonicalKleinCore_isPGroup
    (hr : Nat.card block.Fibre = 4) {G : Type} [Group G]
    (eG : DegreeFourComplementQuotient block P ≃* G) (K : Subgroup G)
    (hK : IsPGroup 2 K) :
    IsPGroup 2 (originalCanonicalKleinCore block P eG K) := by
  apply (hK.comap_of_injective eG.toMonoidHom eG.injective).comap_of_ker_isPGroup
  let e := MulEquiv.subgroupCongr (QuotientGroup.ker_mk' (E block P))
  exact (degreeFour_translationIntersection_isPGroup block P hr).of_injective
    e.toMonoidHom e.injective

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
