import SymmetricSubgroupAsymptotics.PrimitiveAffineOriginalPhysicalFibreCharts
import SymmetricSubgroupAsymptotics.PrimitiveAffineOriginalTranslationPointFreeness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourNonzeroCore
import SymmetricSubgroupAsymptotics.BinaryFourLocalInvolutionPointGauge

/-! A nonidentity original translation coordinate gives the moving
physical fibre chart internally. Its normalized vector is the explicit
nonzero vector (1,0), and the actual original element is retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinaryFourBlockAugmentation

theorem originalTranslationMovingFibreChart
    {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre] (hr : Nat.card block.Fibre = 4)
    (i : block.Points) (z : E block P)
    (hne : (ambientEmbedding block (z : preE7NonPairAction w U)).left i ≠ 1) :
    ∃ a : Local ≃ originalBlockFibre block.map i,
      ∀ v : Local, (a (v + ![1,0])).1 =
        (z : preE7NonPairAction w U) • (a v).1 := by
  let b : Local ≃ block.Fibre := BinaryFourLocalCubicPointGauge.pointEquiv.symm.trans
    (Finite.equivFinOfCardEq hr).symm
  let raw := b.trans (originalPhysicalFibreEquiv block i)
  let ell := (ambientEmbedding block (z : preE7NonPairAction w U)).left i
  let t : Equiv.Perm Local := b.symm.permCongrHom ell.1
  have hright : (ambientEmbedding block (z : preE7NonPairAction w U)).right = 1 :=
    ((PermutationalWreathProduct.mem_mapBase_ker_iff (localMap block P)
      (ambientEmbedding block (z : preE7NonPairAction w U))).mp z.2).1
  have hi : (z : preE7NonPairAction w U) • i = i := by
    change (ambientEmbedding block (z : preE7NonPairAction w U)).right • i = i
    rw [hright,one_smul]
  have hraw (v : Local) : (raw (t v)).1 =
      (z : preE7NonPairAction w U) • (raw v).1 := by
    change (originalPhysicalFibreEquiv block i (b (b.symm (ell.1 (b v))))).1 =
      (z : preE7NonPairAction w U) • (originalPhysicalFibreEquiv block i (b v)).1
    rw [b.apply_symm_apply]
    exact congrArg Subtype.val
      (originalPhysicalFibreEquiv_action block i (z : preE7NonPairAction w U) hi (b v))
  have ht : t^2 = 1 := by
    apply Equiv.ext
    intro v
    apply raw.injective
    apply Subtype.ext
    change (raw (t (t v))).1 = (raw v).1
    rw [hraw,hraw]
    have hz := congrArg Subtype.val (degreeFour_translation_pow_two block P hr z)
    simpa only [pow_two,mul_smul,one_smul] using congrArg
      (fun g : preE7NonPairAction w U => g • (raw v).1) hz
  have hfree : ∀ v : Local, t v ≠ v := by
    intro v h
    apply originalTranslationCoordinate_fixed_free block P i z hne (b v)
    have h' := congrArg b h
    change b (b.symm (ell.1 (b v))) = b v at h'
    rw [b.apply_symm_apply] at h'
    exact h'
  obtain ⟨e,he⟩ := BinaryFourLocalInvolutionPointGauge.translation_gauge t ht hfree
  refine ⟨e.symm.trans raw,?_⟩
  intro v
  have h := congrArg (fun a : Equiv.Perm Local => a v) he
  change e (t (e.symm v)) = v + ![1,0] at h
  have h' := congrArg e.symm h
  rw [e.symm_apply_apply] at h'
  change (raw (e.symm (v + ![1,0]))).1 =
    (z : preE7NonPairAction w U) • (raw (e.symm v)).1
  rw [← h']
  exact hraw (e.symm v)

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
