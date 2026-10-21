import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Lean.Elab.Tactic.Omega

/-! A right-exact coinvariant sequence retains a specified denominator
already killed in the middle source head. This is the generic linear
filtration needed by the next actual pair-module width bounds. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.RepresentationCoinvariantExactDenominator

variable {k G V W Z : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup Z] [Module k Z]
  {rho : Representation k G V} {sigma : Representation k G W}
  {tau : Representation k G Z}

theorem coinvariantsKer_map_of_surjective
    (q : rho.IntertwiningMap tau) (hq : Function.Surjective q) :
    (Representation.Coinvariants.ker rho).map q.toLinearMap =
      Representation.Coinvariants.ker tau := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    change q (rho g v - v) ∈ Representation.Coinvariants.ker tau
    rw [map_sub, Representation.IntertwiningMap.isIntertwining rho tau q g v]
    exact Representation.Coinvariants.sub_mem_ker g (q v)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, z⟩, rfl⟩
    obtain ⟨v, rfl⟩ := hq z
    refine ⟨rho g v - v, Representation.Coinvariants.sub_mem_ker g v, ?_⟩
    change q (rho g v - v) = tau g (q v) - q v
    rw [map_sub, Representation.IntertwiningMap.isIntertwining rho tau q g v]

/-- Coinvariants preserve exactness at the middle and final terms. -/
theorem coinvariant_range_eq_ker
    (i : sigma.IntertwiningMap rho) (q : rho.IntertwiningMap tau)
    (hq : Function.Surjective q) (hexact : i.toLinearMap.range = q.toLinearMap.ker) :
    ((Representation.Coinvariants.mk rho).comp i.toLinearMap).range =
      (Representation.Coinvariants.map rho tau q).ker := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    change Representation.Coinvariants.mk tau (q (i a)) = 0
    have ha : i a ∈ q.toLinearMap.ker := hexact.le ⟨a, rfl⟩
    rw [show q (i a) = 0 from ha, map_zero]
  · intro x hx
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective rho x
    have hz : q v ∈ Representation.Coinvariants.ker tau :=
      (Representation.Coinvariants.mk_eq_zero tau).mp hx
    rw [← coinvariantsKer_map_of_surjective q hq] at hz
    obtain ⟨r, hr, he⟩ := hz
    change q r = q v at he
    have hvr : v - r ∈ q.toLinearMap.ker := by
      change q (v - r) = 0
      rw [map_sub, he, sub_self]
    obtain ⟨a, ha⟩ := hexact.ge hvr
    change i a = v - r at ha
    refine ⟨a, ?_⟩
    change Representation.Coinvariants.mk rho (i a) = Representation.Coinvariants.mk rho v
    apply (Representation.Coinvariants.mk_eq_iff rho).mpr
    rw [ha]
    simpa only [sub_sub_cancel_left] using (Representation.Coinvariants.ker rho).neg_mem hr

/-- An explicit denominator killed in the original head is paid before
the left layer's dimension. No splitting or invariant lifting is assumed. -/
theorem finrank_coinvariants_le_quotient_add
    [FiniteDimensional k V] [FiniteDimensional k W] [FiniteDimensional k Z]
    (i : sigma.IntertwiningMap rho) (q : rho.IntertwiningMap tau)
    (hq : Function.Surjective q) (hexact : i.toLinearMap.range = q.toLinearMap.ker)
    (P : Submodule k W)
    (hP : P ≤ ((Representation.Coinvariants.mk rho).comp i.toLinearMap).ker) :
    Module.finrank k rho.Coinvariants ≤
      Module.finrank k (W ⧸ P) + Module.finrank k tau.Coinvariants := by
  let a := (Representation.Coinvariants.mk rho).comp i.toLinearMap
  let aP := P.liftQ a hP
  have harange : aP.range = a.range := by
    ext x
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨w, rfl⟩ := P.mkQ_surjective v
      exact ⟨w, hv⟩
    · rintro ⟨w, rfl⟩
      exact ⟨P.mkQ w, rfl⟩
  let b := Representation.Coinvariants.map rho tau q
  have he : aP.range = b.ker := harange.trans (coinvariant_range_eq_ker i q hq hexact)
  have hb := b.finrank_range_add_finrank_ker
  have hi := aP.finrank_range_le
  have hq' := Submodule.finrank_le b.range
  rw [he] at hi
  omega

end SymmetricSubgroupAsymptotics.RepresentationCoinvariantExactDenominator
