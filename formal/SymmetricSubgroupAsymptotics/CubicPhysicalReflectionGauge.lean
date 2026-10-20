import SymmetricSubgroupAsymptotics.BinaryFourLocalCubicPointGauge

/-! Simultaneous cubic/reflection coordinates on an actual four-point
fibre. All group relations are transported through the actual action. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CubicPhysicalReflectionGauge
open BinaryFourBlockAugmentation

theorem exists_gauge {G X : Type} [Group G] [MulAction G X]
    (s g : G) (hg : g^2 = 1) (hgs : g*s*g⁻¹ = s⁻¹)
    (a : Local ≃ X) (ha : ∀ v, a (localCycle v) = s • a v) :
    ∃ b : Local ≃ X,
      (∀ v, b (localCycle v) = s • b v) ∧
      ∀ v, b (BinaryFourLocalCubicPointGauge.reflection v) = g • b v := by
  let f : G →* Equiv.Perm Local :=
    a.symm.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G X)
  have hf (h : G) (v : Local) : a (f h v) = h • a v := by
    change a (a.symm (h • a v)) = h • a v
    exact a.apply_symm_apply (h • a v)
  have hfs : f s = localCycle.toEquiv := by
    apply Equiv.ext
    intro v
    apply a.injective
    exact (hf s v).trans (ha v).symm
  have hc : (f s)^3 = 1 := by rw [hfs]; decide +kernel
  have hcn : f s ≠ 1 := by rw [hfs]; decide +kernel
  have ht : (f g)^2 = 1 := by rw [← map_pow,hg,map_one]
  have hconj : f g*f s*(f g)⁻¹ = (f s)⁻¹ := by
    rw [← map_inv,← map_mul,← map_mul,hgs,map_inv]
  obtain ⟨e,hes,heg⟩ := BinaryFourLocalCubicPointGauge.cubic_involution_gauge
    (f s) (f g) hc hcn ht hconj
  refine ⟨e.symm.trans a,?_,?_⟩
  · intro v
    have he := congrArg (fun p : Equiv.Perm Local => e.symm (p v)) hes
    change e.symm (e (f s (e.symm v))) = e.symm (localCycle v) at he
    rw [e.symm_apply_apply] at he
    change a (e.symm (localCycle v)) = s • a (e.symm v)
    rw [← he]
    exact hf s (e.symm v)
  · intro v
    have he := congrArg (fun p : Equiv.Perm Local => e.symm (p v)) heg
    change e.symm (e (f g (e.symm v))) =
      e.symm (BinaryFourLocalCubicPointGauge.reflection v) at he
    rw [e.symm_apply_apply] at he
    change a (e.symm (BinaryFourLocalCubicPointGauge.reflection v)) = g • a (e.symm v)
    rw [← he]
    exact hf g (e.symm v)

end SymmetricSubgroupAsymptotics.CubicPhysicalReflectionGauge
