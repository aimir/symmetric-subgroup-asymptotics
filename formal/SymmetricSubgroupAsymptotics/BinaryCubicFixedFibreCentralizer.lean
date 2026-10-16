import SymmetricSubgroupAsymptotics.BinaryFourLocalCubicPointGauge
import SymmetricSubgroupAsymptotics.BinaryFourCubicNormalizerPointShapes

/-! An involution commuting with the cubic Singer action fixes its whole
four-point fibre. This acts on the actual physical points through the
constructed fibre chart; it is not a bound on an ambient substitute. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCubicFixedFibreCentralizer
open BinaryFourBlockAugmentation
local instance : DecidableEq Local := BinaryFourLocalCubicPointGauge.pointDecidableEq

theorem pointwise (t : Local → Local)
    (ht : ∀ v : Local, t (t v) = v)
    (hc : ∀ v : Local, t (localCycle v) = localCycle (t v)) :
    ∀ v : Local, t v = v := by
  let p := BinaryFourLocalCubicPointGauge.pointEquiv
  let c := BinaryFourCubicNormalizerPointShapes.blockCycle
  have hp : ∀ j : Fin 4, p (c j)=localCycle (p j) := by decide +kernel
  have hpi (v : Local) : p.symm (localCycle v)=c (p.symm v) := by
    apply p.injective
    rw [p.apply_symm_apply,hp,p.apply_symm_apply]
  let u : Fin 4 → Fin 4 := fun j => p.symm (t (p j))
  have hu (j : Fin 4) : u (u j)=j := by
    change p.symm (t (p (p.symm (t (p j)))))=j
    rw [p.apply_symm_apply,ht,p.symm_apply_apply]
  have huc (j : Fin 4) : u (c j)=c (u j) := by
    change p.symm (t (p (c j)))=c (p.symm (t (p j)))
    rw [hp,hc,hpi]
  have finite : ∀ u : Fin 4 → Fin 4,
      (∀ j,u (u j)=j) → (∀ j,u (c j)=c (u j)) → ∀ j,u j=j := by
    decide +kernel
  intro v
  have h := congrArg p (finite u hu huc (p.symm v))
  change p (p.symm (t (p (p.symm v))))=p (p.symm v) at h
  simpa only [p.apply_symm_apply] using h

theorem actual_fibre_fixed {G X : Type} [Group G] [MulAction G X]
    (F : X → Prop) (a : Local ≃ {x : X // F x}) (s e : G)
    (ha : ∀ v : Local, (a (localCycle v)).1 = s • (a v).1)
    (he : ∀ x : X, F x → F (e • x)) (he2 : e^2 = 1)
    (hcommute : ∀ x : X, e • (s • x) = s • (e • x)) :
    ∀ v : Local, e • (a v).1 = (a v).1 := by
  let t : Local → Local := fun v => a.symm ⟨e • (a v).1,he _ (a v).2⟩
  have hraw (v : Local) : (a (t v)).1 = e • (a v).1 := by
    exact congrArg Subtype.val (a.apply_symm_apply ⟨e • (a v).1,he _ (a v).2⟩)
  have ht (v : Local) : t (t v) = v := by
    apply a.injective
    apply Subtype.ext
    rw [hraw,hraw]
    simpa only [pow_two,mul_smul,one_smul] using
      congrArg (fun g : G => g • (a v).1) he2
  have hc (v : Local) : t (localCycle v) = localCycle (t v) := by
    apply a.injective
    apply Subtype.ext
    rw [hraw,ha,ha,hraw,hcommute]
  intro v
  rw [← hraw,pointwise t ht hc v]

end SymmetricSubgroupAsymptotics.BinaryCubicFixedFibreCentralizer
