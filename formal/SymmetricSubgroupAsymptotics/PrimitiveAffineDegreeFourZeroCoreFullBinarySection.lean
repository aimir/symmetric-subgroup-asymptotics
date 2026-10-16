import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreSelectedBinarySection

/-! Full binary-socle instantiation: the selector is True, so central
trivial constituents remain in the same actual elementary-section maps. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]

local instance degreeFourFullBinarySection_profilePrimeFact : Fact P.p.Prime := ⟨P.p_prime⟩

def degreeFourFullBinarySelector
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (_ : Subgroup (DegreeFourRetainedQuotient N)) : Prop := True

abbrev DegreeFourFullBinarySocle :=
  DegreeFourSelectedBinarySocle block P (degreeFourFullBinarySelector (w := w) (U := U))

abbrev DegreeFourFullBinarySocleChart :=
  DegreeFourSelectedBinarySocleChart block P (degreeFourFullBinarySelector (w := w) (U := U))

abbrev DegreeFourFullBinaryTranslationIntersection :=
  DegreeFourSelectedBinaryTranslationIntersection block P (degreeFourFullBinarySelector (w := w) (U := U))

abbrev DegreeFourFullBinaryTranslationPreimage :=
  DegreeFourSelectedBinaryTranslationPreimage block P (degreeFourFullBinarySelector (w := w) (U := U))

abbrev DegreeFourFullBinarySourceSection :=
  DegreeFourSelectedBinarySourceSection block P (degreeFourFullBinarySelector (w := w) (U := U))

abbrev DegreeFourFullBinaryTargetSection :=
  DegreeFourSelectedBinaryTargetSection block P (degreeFourFullBinarySelector (w := w) (U := U))

abbrev DegreeFourFullBinarySourceSectionInflated :=
  DegreeFourSelectedBinarySourceSectionInflated block P (degreeFourFullBinarySelector (w := w) (U := U))

abbrev degreeFourFullBinarySocleTopMap :=
  degreeFourSelectedBinarySocleTopMap block P (degreeFourFullBinarySelector (w := w) (U := U))

abbrev degreeFourFullBinaryTranslationIntersectionHom :=
  degreeFourSelectedBinaryTranslationIntersectionHom block P (degreeFourFullBinarySelector (w := w) (U := U))

abbrev degreeFourFullBinarySourceIntersectionEquiv :=
  degreeFourSelectedBinarySourceIntersectionEquiv block P (degreeFourFullBinarySelector (w := w) (U := U))

abbrev degreeFourFullBinaryTargetIntersectionEquiv :=
  degreeFourSelectedBinaryTargetIntersectionEquiv block P (degreeFourFullBinarySelector (w := w) (U := U))

abbrev degreeFourFullBinaryTranslationSectionMulHom :=
  degreeFourSelectedBinaryTranslationSectionMulHom block P (degreeFourFullBinarySelector (w := w) (U := U))

abbrev degreeFourFullBinaryTranslationSectionAddHom :=
  degreeFourSelectedBinaryTranslationSectionAddHom block P (degreeFourFullBinarySelector (w := w) (U := U))

abbrev degreeFourFullBinaryTranslationSectionLinearMap :=
  degreeFourSelectedBinaryTranslationSectionLinearMap block P (degreeFourFullBinarySelector (w := w) (U := U))

abbrev degreeFourFullBinaryTranslationIntersectionHom_surjective :=
  degreeFourSelectedBinaryTranslationIntersectionHom_surjective block P (degreeFourFullBinarySelector (w := w) (U := U))

abbrev degreeFourFullBinaryTranslationSectionMulHom_surjective :=
  degreeFourSelectedBinaryTranslationSectionMulHom_surjective block P (degreeFourFullBinarySelector (w := w) (U := U))

abbrev degreeFourFullBinaryTranslationSectionLinearMap_surjective :=
  degreeFourSelectedBinaryTranslationSectionLinearMap_surjective block P (degreeFourFullBinarySelector (w := w) (U := U))

abbrev degreeFourFullBinaryTranslationIntersectionHom_conj :=
  degreeFourSelectedBinaryTranslationIntersectionHom_conj block P (degreeFourFullBinarySelector (w := w) (U := U))

abbrev degreeFourFullBinarySourceIntersectionEquiv_action :=
  degreeFourSelectedBinarySourceIntersectionEquiv_action block P (degreeFourFullBinarySelector (w := w) (U := U))

abbrev degreeFourFullBinaryTargetIntersectionEquiv_action :=
  degreeFourSelectedBinaryTargetIntersectionEquiv_action block P (degreeFourFullBinarySelector (w := w) (U := U))

abbrev degreeFourFullBinaryTranslationSectionMulHom_equivariant :=
  degreeFourSelectedBinaryTranslationSectionMulHom_equivariant block P (degreeFourFullBinarySelector (w := w) (U := U))

abbrev degreeFourFullBinaryTranslationSectionLinearMap_equivariant :=
  degreeFourSelectedBinaryTranslationSectionLinearMap_equivariant block P (degreeFourFullBinarySelector (w := w) (U := U))

abbrev degreeFourFullBinaryTranslationSectionIntertwiner :=
  degreeFourSelectedBinaryTranslationSectionIntertwiner block P (degreeFourFullBinarySelector (w := w) (U := U))

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
