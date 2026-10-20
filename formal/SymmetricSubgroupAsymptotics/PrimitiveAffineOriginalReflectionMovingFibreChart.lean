import SymmetricSubgroupAsymptotics.PrimitiveAffineOriginalPhysicalFibreCharts
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourLocalInvolutionFixedPoint
import SymmetricSubgroupAsymptotics.BinaryFourLocalInvolutionPointGauge

/-! A genuine odd local quotient involution supplies the moving physical
reflection chart. Its fixed point is derived from the literal regular
translation subgroup, not assumed as a point certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinaryFourBlockAugmentation

theorem originalReflectionMovingFibreChart
    {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre] (hr : Nat.card block.Fibre = 4)
    (i : block.Points) (g : preE7NonPairAction w U) (hi : g • i = i)
    (hg : g^2=1)
    (hne : localMap block P ((ambientEmbedding block g).left i) ≠ 1) :
    ∃ a : Local ≃ originalBlockFibre block.map i,
      ∀ v, (a (BinaryFourLocalCubicPointGauge.reflection v)).1 = g • (a v).1 := by
  let b : Local ≃ block.Fibre := BinaryFourLocalCubicPointGauge.pointEquiv.symm.trans
    (Finite.equivFinOfCardEq hr).symm
  let raw := b.trans (originalPhysicalFibreEquiv block i)
  let ell := (ambientEmbedding block g).left i
  let t : Equiv.Perm Local := b.symm.permCongrHom ell.1
  have hraw (v : Local) : (raw (t v)).1 = g • (raw v).1 := by
    change (originalPhysicalFibreEquiv block i (b (b.symm (ell.1 (b v))))).1 =
      g • (originalPhysicalFibreEquiv block i (b v)).1
    rw [b.apply_symm_apply]
    exact congrArg Subtype.val (originalPhysicalFibreEquiv_action block i g hi (b v))
  have ht : t^2=1 := by
    apply Equiv.ext
    intro v
    apply raw.injective
    apply Subtype.ext
    change (raw (t (t v))).1 = (raw v).1
    rw [hraw,hraw]
    simpa only [pow_two,mul_smul,one_smul] using congrArg
      (fun h : preE7NonPairAction w U => h • (raw v).1) hg
  have hell2 : ell^2=1 := by
    apply Subtype.ext
    apply b.symm.permCongrHom.injective
    change b.symm.permCongrHom (ell.1^2) = b.symm.permCongrHom 1
    rw [map_pow,map_one]
    exact ht
  have htn : t≠1 := by
    intro h
    apply hne
    have he : ell=1 := by
      apply Subtype.ext
      apply b.symm.permCongrHom.injective
      exact h.trans b.symm.permCongrHom.map_one.symm
    exact (congrArg (localMap block P) he).trans (localMap block P).map_one
  obtain ⟨x,hx⟩ := degreeFourLocalInvolutionFixedPoint block P hr ell hell2 hne
  have hfix : ∃ v : Local, t v=v := by
    refine ⟨b.symm x,?_⟩
    change b.symm (ell.1 (b (b.symm x))) = b.symm x
    rw [b.apply_symm_apply]
    exact congrArg b.symm hx
  obtain ⟨e,he⟩ := BinaryFourLocalInvolutionPointGauge.reflection_gauge t ht htn hfix
  refine ⟨e.symm.trans raw,?_⟩
  intro v
  have h := congrArg (fun p : Equiv.Perm Local => e.symm (p v)) he
  change e.symm (e (t (e.symm v))) =
    e.symm (BinaryFourLocalCubicPointGauge.reflection v) at h
  rw [e.symm_apply_apply] at h
  change (raw (e.symm (BinaryFourLocalCubicPointGauge.reflection v))).1 =
    g • (raw (e.symm v)).1
  rw [←h]
  exact hraw (e.symm v)

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
