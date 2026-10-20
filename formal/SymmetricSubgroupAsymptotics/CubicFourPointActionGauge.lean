import SymmetricSubgroupAsymptotics.BinaryFourLocalCubicPointGauge
import SymmetricSubgroupAsymptotics.BinaryFourCubicNormalizerPointShapes

/-! An actual nonidentity cubic permutation on four actual blocks gives
the normalized block chart internally. No cycle chart is a premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CubicFourPointActionGauge
open BinaryFourBlockAugmentation BinaryFourCubicNormalizerPointShapes

theorem exists_gauge {G I : Type} [Group G] [MulAction G I] [Finite I]
    (hcard : Nat.card I = 4) (s : G) (hs : s^3 = 1)
    (hne : MulAction.toPermHom G I s ≠ 1) :
    ∃ d : I ≃ Fin 4, ∀ i : I, d (s • i) = blockCycle (d i) := by
  let p := BinaryFourLocalCubicPointGauge.pointEquiv
  let b : I ≃ Local := (Finite.equivFinOfCardEq hcard).trans p
  let c : Equiv.Perm Local := b.permCongrHom (MulAction.toPermHom G I s)
  have hc : c^3 = 1 := by
    change (b.permCongrHom (MulAction.toPermHom G I s))^3 = 1
    rw [← map_pow,← map_pow,hs,map_one,map_one]
  have hcn : c ≠ 1 := by
    intro h
    apply hne
    apply b.permCongrHom.injective
    exact h.trans b.permCongrHom.map_one.symm
  obtain ⟨e,he⟩ := BinaryFourLocalCubicPointGauge.cubic_gauge c hc hcn
  have hpoint (v : Local) : p (blockCycle (p.symm v)) = localCycle v := by
    revert v
    decide +kernel
  refine ⟨b.trans (e.trans p.symm),?_⟩
  intro i
  apply p.injective
  change p (p.symm (e (b (s • i)))) = p (blockCycle (p.symm (e (b i))))
  rw [p.apply_symm_apply,hpoint]
  have h := congrArg (fun a : Equiv.Perm Local => a (e (b i))) he
  change e (c (e.symm (e (b i)))) = localCycle (e (b i)) at h
  rw [e.symm_apply_apply] at h
  change e (b (s • b.symm (b i))) = localCycle (e (b i)) at h
  rw [b.symm_apply_apply] at h
  exact h

end SymmetricSubgroupAsymptotics.CubicFourPointActionGauge
