import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveBlockTransfer

/-! Point freeness of the unchanged original translation coordinates.
This binds the regular-translation lemma to the actual wreath embedding,
before any local point relabelling or normal quotient is selected. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]

def originalTranslationCoordinate (i : block.Points) (e : E block P) : P.V := by
  let k := PermutationalWreathProduct.Compression.kernelCoordinate
    (ambientEmbedding block) (localMap block P) i e
  exact ⟨k.1, by rw [← localMap_ker block P]; exact k.2⟩

theorem originalTranslationCoordinate_val (i : block.Points) (e : E block P) :
    (originalTranslationCoordinate block P i e : block.Component) =
      (ambientEmbedding block (e : preE7NonPairAction w U)).left i := rfl

theorem originalTranslationCoordinate_eq_one_of_fixed
    (i : block.Points) (e : E block P) (x : block.Fibre)
    (hfix : ((ambientEmbedding block (e : preE7NonPairAction w U)).left i) • x = x) :
    originalTranslationCoordinate block P i e = 1 :=
  P.eq_one_of_smul_eq x (originalTranslationCoordinate block P i e) hfix

theorem originalTranslationCoordinate_fixed_free
    (i : block.Points) (e : E block P)
    (hne : (ambientEmbedding block (e : preE7NonPairAction w U)).left i ≠ 1) :
    ∀ x : block.Fibre,
      ((ambientEmbedding block (e : preE7NonPairAction w U)).left i) • x ≠ x := by
  intro x hfix
  apply hne
  have h := congrArg Subtype.val
    (originalTranslationCoordinate_eq_one_of_fixed block P i e x hfix)
  exact h

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
