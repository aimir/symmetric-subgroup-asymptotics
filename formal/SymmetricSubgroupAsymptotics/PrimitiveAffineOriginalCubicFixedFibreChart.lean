import SymmetricSubgroupAsymptotics.PrimitiveAffineOriginalPhysicalFibreCharts
import SymmetricSubgroupAsymptotics.PrimitiveAffineBinaryExceptionalLocal

/-! Normalize the actual fixed physical fibre of an original cubic
element. Faithfulness is the actual local quotient map; the physical
chart itself is constructed, including its action equation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinaryFourBlockAugmentation

theorem originalCubicFixedFibreChart
    {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre] (hr : Nat.card block.Fibre = 4)
    (i : block.Points) (s : preE7NonPairAction w U) (hi : s • i = i)
    (hs : s^3 = 1) (hne : QuotientGroup.mk' (E block P) s ≠ 1)
    (hlocal : Function.Injective (binaryAffineStabilizerComponent block P i)) :
    ∃ a : Local ≃ originalBlockFibre block.map i,
      ∀ v : Local, (a (localCycle v)).1 = s • (a v).1 := by
  let b : Local ≃ block.Fibre := BinaryFourLocalCubicPointGauge.pointEquiv.symm.trans
    (Finite.equivFinOfCardEq hr).symm
  let raw := b.trans (originalPhysicalFibreEquiv block i)
  let ell := (ambientEmbedding block s).left i
  let c : Equiv.Perm Local := b.symm.permCongrHom ell.1
  let q : binaryAffineQuotientTopStabilizer block P i :=
    ⟨QuotientGroup.mk' (E block P) s, by change s • i = i; exact hi⟩
  have hell : ell ≠ 1 := by
    intro h
    have hq : binaryAffineStabilizerComponent block P i q = 1 := by
      change localMap block P ell = 1
      rw [h,map_one]
    have hq' : q = 1 := hlocal
      (hq.trans (binaryAffineStabilizerComponent block P i).map_one.symm)
    exact hne (congrArg Subtype.val hq')
  have hcn : c ≠ 1 := by
    intro h
    apply hell
    apply Subtype.ext
    apply b.symm.permCongrHom.injective
    exact h.trans b.symm.permCongrHom.map_one.symm
  have hraw (v : Local) : (raw (c v)).1 = s • (raw v).1 := by
    change (originalPhysicalFibreEquiv block i
      (b (b.symm (ell.1 (b v))))).1 =
      s • (originalPhysicalFibreEquiv block i (b v)).1
    rw [b.apply_symm_apply]
    exact congrArg Subtype.val (originalPhysicalFibreEquiv_action block i s hi (b v))
  have hc : c^3 = 1 := by
    apply Equiv.ext
    intro v
    apply raw.injective
    apply Subtype.ext
    change (raw (c (c (c v)))).1 = (raw v).1
    rw [hraw,hraw,hraw]
    simpa [pow_succ,mul_smul] using congrArg
      (fun g : preE7NonPairAction w U => g • (raw v).1) hs
  obtain ⟨e,he⟩ := BinaryFourLocalCubicPointGauge.cubic_gauge c hc hcn
  refine ⟨e.symm.trans raw,?_⟩
  intro v
  have h := congrArg (fun a : Equiv.Perm Local => a v) he
  change e (c (e.symm v)) = localCycle v at h
  have h' := congrArg e.symm h
  rw [e.symm_apply_apply] at h'
  change (raw (e.symm (localCycle v))).1 = s • (raw (e.symm v)).1
  rw [← h']
  exact hraw (e.symm v)

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
