import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourOriginalBinarySocleCoreFixed

/-! The unchanged original quotient maps supplying the literal-L factor:
A4 maps into the even subgroup, S4 onto the full symmetric complement.
Both maps have actual normal-binary Klein preimages fixing the target. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

open BinaryFourBlockAugmentation BinaryFourSymmetricBlockActions

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]

local instance primitiveAffineDegreeFourOriginalCanonicalCoreAction_localFact1 : Fact P.p.Prime := ⟨P.p_prime⟩

namespace DegreeFourS4OriginalPointChart

variable (C : DegreeFourS4OriginalPointChart block)

def canonicalMap (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥) :
    preE7NonPairAction w U →* SymmetricComplement :=
  ((groupEquiv (block := block) (P := P) (C := C) hr hD)).toMonoidHom.comp (QuotientGroup.mk' (E block P))

theorem canonicalMap_surjective (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) :
    Function.Surjective ((canonicalMap (block := block) (P := P) (C := C) hr hD)) :=
  ((groupEquiv (block := block) (P := P) (C := C) hr hD)).surjective.comp (QuotientGroup.mk'_surjective (E block P))

theorem canonicalMap_even_lifts (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) :
    ∀ r : Complement, ∃ g : preE7NonPairAction w U,
      (canonicalMap (block := block) (P := P) (C := C) hr hD) g = SemidirectProduct.inl r :=
  fun r => (canonicalMap_surjective (block := block) (P := P) (C := C) hr hD) (SemidirectProduct.inl r)

theorem binaryTarget_fixed_by_canonicalKlein (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (g : preE7NonPairAction w U)
    (hg : (canonicalMap (block := block) (P := P) (C := C) hr hD) g ∈ BinaryFourSymmetricKleinNormalCover.klein)
    (v : (DegreeFourFullBinaryTargetSection block P N).toSubmodule) :
    (DegreeFourFullBinaryTargetSection block P N).toRepresentation
      (degreeFourFullBinarySocleTopMap block P N g) v = v := by
  let K := originalCanonicalKleinCore block P ((groupEquiv (block := block) (P := P) (C := C) hr hD))
    BinaryFourSymmetricKleinNormalCover.klein
  have hK : IsPGroup 2 K := originalCanonicalKleinCore_isPGroup block P hr _ _
    BinaryFourCanonicalBinaryCores.s4_klein_isPGroup
  exact degreeFourFullBinaryTargetSection_original_normal_binary_fixed block P hr N K hK ⟨g, hg⟩ v

end DegreeFourS4OriginalPointChart

namespace DegreeFourA4OriginalPointChart

variable (C : DegreeFourA4OriginalPointChart block)

def canonicalMap (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥) :
    preE7NonPairAction w U →* SymmetricComplement :=
  SemidirectProduct.inl.comp
    (((groupEquiv (block := block) (P := P) (C := C) hr hD)).toMonoidHom.comp (QuotientGroup.mk' (E block P)))

theorem canonicalMap_even_lifts (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) :
    ∀ r : Complement, ∃ g : preE7NonPairAction w U,
      (canonicalMap (block := block) (P := P) (C := C) hr hD) g = SemidirectProduct.inl r := by
  intro r
  obtain ⟨g, hg⟩ := ((groupEquiv (block := block) (P := P) (C := C) hr hD)).surjective.comp
    (QuotientGroup.mk'_surjective (E block P)) r
  exact ⟨g, congrArg SemidirectProduct.inl hg⟩

theorem binaryTarget_fixed_by_canonicalKlein (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (g : preE7NonPairAction w U)
    (hg : (canonicalMap (block := block) (P := P) (C := C) hr hD) g ∈ BinaryFourSymmetricKleinNormalCover.klein)
    (v : (DegreeFourFullBinaryTargetSection block P N).toSubmodule) :
    (DegreeFourFullBinaryTargetSection block P N).toRepresentation
      (degreeFourFullBinarySocleTopMap block P N g) v = v := by
  let K := originalCanonicalKleinCore block P ((groupEquiv (block := block) (P := P) (C := C) hr hD))
    BinaryKleinTernaryNormalChain.kleinKernel
  have hK : IsPGroup 2 K := originalCanonicalKleinCore_isPGroup block P hr _ _
    BinaryFourCanonicalBinaryCores.a4_klein_isPGroup
  have hgK : g ∈ K :=
    (BinaryFourSymmetricKleinNormalCover.inl_mem_klein _).mp hg
  exact degreeFourFullBinaryTargetSection_original_normal_binary_fixed block P hr N K hK ⟨g, hgK⟩ v

end DegreeFourA4OriginalPointChart

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
