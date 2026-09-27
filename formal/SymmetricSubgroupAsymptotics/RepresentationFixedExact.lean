import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Lean.Elab.Tactic.Omega

/-! Fixed vectors retain exactness at the first two terms of an actual
sequence of intertwining maps. The dimension bound does not assume that
the last map is onto, that invariant vectors lift through it, or that the
source group is finite. No averaging or semisimplicity is used. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.RepresentationFixedExact

section Map

variable {k G V W : Type*} [CommRing k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W}

/-- Restrict the original intertwiner to its entire original fixed spaces. -/
def fixedMap (f : ρ.IntertwiningMap σ) : ρ.invariants →ₗ[k] σ.invariants :=
  (f.toLinearMap.comp ρ.invariants.subtype).codRestrict σ.invariants (fun v g =>
    (Representation.IntertwiningMap.isIntertwining ρ σ f g v.val).symm.trans
      (congrArg f (v.property g)))

@[simp] theorem fixedMap_apply (f : ρ.IntertwiningMap σ) (v : ρ.invariants) :
    (fixedMap f v : W)=f v := rfl

theorem fixedMap_injective (f : ρ.IntertwiningMap σ) (hf : Function.Injective f) :
    Function.Injective (fixedMap f) := by
  intro v w h
  apply Subtype.ext
  exact hf (congrArg Subtype.val h)

end Map

section Exact

variable {k G C A B : Type*} [Field k] [Group G]
    [AddCommGroup C] [Module k C] [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B]
    {σ : Representation k G C} {ρ : Representation k G A}
    {τ : Representation k G B}

/-- The original exact sequence remains exact at the middle fixed space.
Injectivity of the first map is what makes every fixed image lift fixed. -/
theorem fixedMap_range_eq_ker (i : σ.IntertwiningMap ρ) (q : ρ.IntertwiningMap τ)
    (hi : Function.Injective i) (hexact : i.toLinearMap.range=q.toLinearMap.ker) :
    (fixedMap i).range=(fixedMap q).ker := by
  apply le_antisymm
  · rintro _ ⟨c,rfl⟩
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    have hc : i.toLinearMap c.val∈q.toLinearMap.ker := hexact.le ⟨c.val,rfl⟩
    exact hc
  · intro a ha
    have hqa : q.toLinearMap a.val=0 :=
      congrArg Subtype.val (LinearMap.mem_ker.mp ha)
    have harange : a.val∈i.toLinearMap.range := hexact.ge hqa
    obtain ⟨c,hc⟩ := harange
    change i c=a.val at hc
    have hcfixed : c∈σ.invariants := by
      intro g
      apply hi
      calc
        i (σ g c)=ρ g (i c) :=
          Representation.IntertwiningMap.isIntertwining σ ρ i g c
        _ = ρ g a.val := by rw [hc]
        _ = a.val := a.property g
        _ = i c := hc.symm
    exact ⟨⟨c,hcfixed⟩,Subtype.ext hc⟩

/-- The required fixed-space dimension inequality for the literal
original intertwiners. The final invariant map need not be surjective. -/
theorem finrank_invariants_le_of_range_eq_ker
    [FiniteDimensional k C] [FiniteDimensional k A] [FiniteDimensional k B]
    (i : σ.IntertwiningMap ρ) (q : ρ.IntertwiningMap τ)
    (hi : Function.Injective i) (hexact : i.toLinearMap.range=q.toLinearMap.ker) :
    Module.finrank k ρ.invariants≤
      Module.finrank k σ.invariants+Module.finrank k τ.invariants := by
  have he := fixedMap_range_eq_ker i q hi hexact
  have hi' := LinearMap.finrank_range_of_inj (fixedMap_injective i hi)
  have hr := (fixedMap q).finrank_range_add_finrank_ker
  have hb := Submodule.finrank_le (fixedMap q).range
  rw [← he,hi'] at hr
  omega

end Exact
end SymmetricSubgroupAsymptotics.RepresentationFixedExact
