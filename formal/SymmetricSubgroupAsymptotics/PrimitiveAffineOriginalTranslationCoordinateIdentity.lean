import SymmetricSubgroupAsymptotics.PrimitiveAffineOriginalPhysicalFibreCharts

/-! A zero literal translation coordinate fixes the entire corresponding
original physical fibre. This is the converse local bridge used to detect
the nonzero moving coordinate of a centralizing original translation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]

theorem originalTranslation_fixes_blocks (z : E block P) (i : block.Points) :
    (z : preE7NonPairAction w U) • i = i := by
  have hright : (ambientEmbedding block (z : preE7NonPairAction w U)).right = 1 :=
    ((PermutationalWreathProduct.mem_mapBase_ker_iff (localMap block P)
      (ambientEmbedding block (z : preE7NonPairAction w U))).mp z.2).1
  change (ambientEmbedding block (z : preE7NonPairAction w U)).right • i = i
  rw [hright,one_smul]

theorem originalTranslationCoordinate_identity_fixes_fibre
    (z : E block P) (i : block.Points)
    (hzero : (ambientEmbedding block (z : preE7NonPairAction w U)).left i = 1)
    (x : Fin w) (hx : block.map x = i) :
    (z : preE7NonPairAction w U) • x = x := by
  obtain ⟨v,hv⟩ := (originalPhysicalFibreEquiv block i).surjective ⟨x,hx⟩
  have h := originalPhysicalFibreEquiv_action block i
    (z : preE7NonPairAction w U) (originalTranslation_fixes_blocks block P z i) v
  rw [hzero,one_smul] at h
  have hv' : (originalPhysicalFibreEquiv block i v).1 = x := congrArg Subtype.val hv
  have h' := congrArg Subtype.val h
  change (originalPhysicalFibreEquiv block i v).1 =
    (z : preE7NonPairAction w U) • (originalPhysicalFibreEquiv block i v).1 at h'
  simpa only [hv'] using h'.symm

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
