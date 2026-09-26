import SymmetricSubgroupAsymptotics.StarAlternatingHead

/-! A nonzero actual subspace of star parameters has its common radical
in the horizontal space. That radical is the ordinary dual coannihilator
of the same parameter subspace. This gives a dimension budget for every
annihilated subspace without enumerating parameter tuples or assuming
that a selected parameter family surjects onto a larger dual space. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {k U : Type*} [Field k] [AddCommGroup U] [Module k U]

/-- The common radical uses exactly the given parameter subspace. -/
def starCommonRadical (L : Submodule k (Module.Dual k U)) : Submodule k (U × k) :=
  ⨅ l : L, (starAlternatingFamily (l : Module.Dual k U)).ker

@[simp] theorem mem_starCommonRadical_iff
    (L : Submodule k (Module.Dual k U)) (x : U × k) :
    x ∈ starCommonRadical L ↔
      ∀ l ∈ L, starAlternatingFamily l x = 0 := by
  simp only [starCommonRadical, Submodule.mem_iInf, LinearMap.mem_ker, Subtype.forall]

/-- A nonzero parameter subspace forces its entire common radical to
have zero last coordinate. -/
theorem starCommonRadical_last_eq_zero
    (L : Submodule k (Module.Dual k U)) (hL : L ≠ ⊥)
    (x : U × k) (hx : x ∈ starCommonRadical L) : x.2 = 0 := by
  classical
  have hle : L ≤ linearJointAnnihilator
      (starAlternatingFamily (k := k) (U := U)) (starCommonRadical L) := by
    intro l hl w hw
    exact (mem_starCommonRadical_iff L w).mp hw l hl
  by_contra ht
  have hz := starAlternatingFamily_joint_eq_bot_of_last_ne_zero
    (starCommonRadical L) x hx ht
  exact hL (le_antisymm (hle.trans hz.le) bot_le)

/-- No direction or parameter is replaced: the exact common radical
is the original parameter space's coannihilator with last coordinate zero. -/
theorem starCommonRadical_eq_horizontal_coannihilator
    (L : Submodule k (Module.Dual k U)) (hL : L ≠ ⊥) :
    starCommonRadical L = L.dualCoannihilator.prod (⊥ : Submodule k k) := by
  ext x
  constructor
  · intro hx
    change x.1 ∈ L.dualCoannihilator ∧ x.2 ∈ (⊥ : Submodule k k)
    constructor
    · apply (Submodule.mem_dualCoannihilator x.1).mpr
      intro l hl
      have h := congrArg (fun f : (U × k) →ₗ[k] k => f (0, 1))
        ((mem_starCommonRadical_iff L x).mp hx l hl)
      simpa only [starAlternatingFamily_apply, map_zero, mul_one, mul_zero,
        sub_zero, LinearMap.zero_apply] using h
    · exact starCommonRadical_last_eq_zero L hL x hx
  · intro hx
    change x.1 ∈ L.dualCoannihilator ∧ x.2 ∈ (⊥ : Submodule k k) at hx
    apply (mem_starCommonRadical_iff L x).mpr
    intro l hl
    apply LinearMap.ext
    intro y
    have hfirst := (Submodule.mem_dualCoannihilator x.1).mp hx.1 l hl
    have hlast : x.2 = 0 := hx.2
    simp only [starAlternatingFamily_apply, hfirst, hlast, zero_mul,
      sub_zero, LinearMap.zero_apply]

/-- Exact dimension budget for the complete common radical of a
nonzero actual parameter subspace. -/
theorem starCommonRadical_finrank_add [FiniteDimensional k U]
    (L : Submodule k (Module.Dual k U)) (hL : L ≠ ⊥) :
    Module.finrank k L + Module.finrank k (starCommonRadical L) =
      Module.finrank k U := by
  have hmap : (starCommonRadical L).map (LinearMap.fst k U k) =
      L.dualCoannihilator := by
    rw [starCommonRadical_eq_horizontal_coannihilator L hL, Submodule.prod_map_fst]
  rw [(starHorizontalEquiv (starCommonRadical L)
      (starCommonRadical_last_eq_zero L hL)).finrank_eq, hmap]
  exact Subspace.finrank_add_finrank_dualCoannihilator_eq L

/-- Any actual W annihilated by every member of a nonzero parameter
subspace shares the same finite dimension budget with that subspace. -/
theorem starAlternatingFamily_finrank_add_parameter_le [FiniteDimensional k U]
    (L : Submodule k (Module.Dual k U)) (W : Submodule k (U × k))
    (hL : L ≠ ⊥)
    (hWL : ∀ l ∈ L, ∀ w ∈ W, starAlternatingFamily l w = 0) :
    Module.finrank k W + Module.finrank k L ≤ Module.finrank k U := by
  have hle : W ≤ starCommonRadical L := by
    intro w hw
    exact (mem_starCommonRadical_iff L w).mpr (fun l hl => hWL l hl w hw)
  calc
    Module.finrank k W + Module.finrank k L ≤
        Module.finrank k (starCommonRadical L) + Module.finrank k L :=
      Nat.add_le_add_right (Submodule.finrank_mono hle) _
    _ = Module.finrank k U := by
      rw [Nat.add_comm, starCommonRadical_finrank_add L hL]

section Transport

variable {L₀ V : Type*} [AddCommGroup L₀] [Module k L₀]
    [AddCommGroup V] [Module k V]

/-- Transport preserves the actual parameter subspace and actual W.
Only genuine full coordinate equivalences and the original pointwise
form identity are used; the subspace P is not assumed to be all parameters. -/
theorem linearFamily_finrank_add_parameter_le_of_star [FiniteDimensional k U]
    (F : L₀ →ₗ[k] (V →ₗ[k] V →ₗ[k] k))
    (eL : L₀ ≃ₗ[k] Module.Dual k U) (eV : V ≃ₗ[k] U × k)
    (hF : ∀ l x y, F l x y = starAlternatingFamily (eL l) (eV x) (eV y))
    (P : Submodule k L₀) (W : Submodule k V) (hP : P ≠ ⊥)
    (hWP : ∀ l ∈ P, ∀ w ∈ W, F l w = 0) :
    Module.finrank k W + Module.finrank k P ≤ Module.finrank k U := by
  have hPmap : P.map eL.toLinearMap ≠ ⊥ := by
    intro hz
    apply hP
    apply le_antisymm _ bot_le
    intro l hl
    have hm : eL l ∈ P.map eL.toLinearMap := ⟨l, hl, rfl⟩
    rw [hz] at hm
    change l = 0
    apply eL.injective
    exact (show eL l = 0 from hm).trans (map_zero eL).symm
  have hWPmap : ∀ l ∈ P.map eL.toLinearMap,
      ∀ w ∈ W.map eV.toLinearMap, starAlternatingFamily l w = 0 := by
    intro l hl w hw
    obtain ⟨a, ha, rfl⟩ := hl
    obtain ⟨x, hx, rfl⟩ := hw
    apply LinearMap.ext
    intro y
    obtain ⟨y, rfl⟩ := eV.surjective y
    change starAlternatingFamily (eL a) (eV x) (eV y) = 0
    exact (hF a x y).symm.trans
      (congrArg (fun f : V →ₗ[k] k => f y) (hWP a ha x hx))
  have h := starAlternatingFamily_finrank_add_parameter_le
    (P.map eL.toLinearMap) (W.map eV.toLinearMap) hPmap hWPmap
  rwa [eV.finrank_map_eq, eL.finrank_map_eq] at h

end Transport

end SymmetricSubgroupAsymptotics
