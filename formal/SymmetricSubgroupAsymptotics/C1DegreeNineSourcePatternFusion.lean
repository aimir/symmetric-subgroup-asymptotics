import SymmetricSubgroupAsymptotics.C1DegreeNineSourcePatternRelabel
import SymmetricSubgroupAsymptotics.FusionOrbitPointing

/-!
# The exact c=1 source pattern passes to the complete fusion source

Let `H ≤ U × Sym(Z)` project onto a transitive retained action `U`, and let
`K` be its literal fusion model on `Ω ⊕ Z`.  Every orbit of the source
projection `J = pr₂(H)` is carried by `inr` onto a literal orbit of `K`, and
the two actual orbit images are identified by that point bijection.  The
retained block is one further orbit, equal to all of `inl Ω`.  If its degree
is not three, the unique-regular-`C3`, no-natural-`A4` pattern of `K` is
therefore the same pattern of `J`.  The complete source subgroup is retained;
no orbit is deleted by an abstract isomorphism.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace FusionSourceOrbits

open OrbitProfileFromOrbits

variable {Ω Z : Type} (U : Subgroup (Equiv.Perm Ω))
    (H : Subgroup (U × Equiv.Perm Z))

/-- The literal fusion model. -/
abbrev model : Subgroup (Equiv.Perm (Ω ⊕ Z)) := H.map (fusionOrbitAction U)

/-- The complete source projection. -/
abbrev source : Subgroup (Equiv.Perm Z) := H.map (MonoidHom.snd U (Equiv.Perm Z))

@[simp] theorem fusionOrbitAction_inr (h : U × Equiv.Perm Z) (z : Z) :
    fusionOrbitAction U h (Sum.inr z) = Sum.inr (h.2 z) := rfl

@[simp] theorem fusionOrbitAction_inl (h : U × Equiv.Perm Z) (x : Ω) :
    fusionOrbitAction U h (Sum.inl x) = Sum.inl ((h.1 : Equiv.Perm Ω) x) := rfl

theorem mem_model_orbit_inr (z : Z) (y : Ω ⊕ Z) :
    y ∈ MulAction.orbit (model U H) (Sum.inr z) ↔
      ∃ z' ∈ MulAction.orbit (source U H) z, y = Sum.inr z' := by
  constructor
  · rintro ⟨⟨k, h, hh, rfl⟩, rfl⟩
    refine ⟨h.2 z, ⟨⟨h.2, h, hh, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨z', ⟨⟨σ, h, hh, rfl⟩, rfl⟩, rfl⟩
    exact ⟨⟨fusionOrbitAction U h, h, hh, rfl⟩, rfl⟩

theorem mem_model_orbit_inl (x : Ω) (y : Ω ⊕ Z) :
    y ∈ MulAction.orbit (model U H) (Sum.inl x) → ∃ x', y = Sum.inl x' := by
  rintro ⟨⟨k, h, hh, rfl⟩, rfl⟩
  exact ⟨(h.1 : Equiv.Perm Ω) x, rfl⟩

/-- The model orbit through the literal image of a source representative. -/
def sourceOrbit (o : Orbit (source U H)) : Orbit (model U H) :=
  Quotient.mk'' (Sum.inr o.out)

theorem orbit_eq_out {X : Type} (G : Subgroup (Equiv.Perm X)) (o : Orbit G) :
    o.orbit = MulAction.orbit G o.out := by
  rw [← MulAction.orbitRel.Quotient.orbit_mk, Quotient.out_eq']

theorem mem_sourceOrbit (o : Orbit (source U H)) (y : Ω ⊕ Z) :
    y ∈ (sourceOrbit U H o).orbit ↔ ∃ z ∈ o.orbit, y = Sum.inr z := by
  rw [sourceOrbit, MulAction.orbitRel.Quotient.orbit_mk, orbit_eq_out]
  exact mem_model_orbit_inr U H o.out y

theorem inr_mem_sourceOrbit (o : Orbit (source U H)) (z : Z) :
    Sum.inr z ∈ (sourceOrbit U H o).orbit ↔ z ∈ o.orbit := by
  rw [mem_sourceOrbit]
  constructor
  · rintro ⟨z', hz', he⟩
    rw [Sum.inr.injEq] at he
    rwa [he]
  · exact fun hz => ⟨z, hz, rfl⟩

/-- The literal point bijection between a source orbit and its model orbit. -/
def sourceOrbitEquiv (o : Orbit (source U H)) :
    o.orbit ≃ (sourceOrbit U H o).orbit where
  toFun z := ⟨Sum.inr z.1, (inr_mem_sourceOrbit U H o z.1).mpr z.2⟩
  invFun y := ⟨Sum.getRight? y.1 |>.getD o.out, by
    obtain ⟨z, hz, hy⟩ := (mem_sourceOrbit U H o y.1).mp y.2
    rw [hy]
    exact hz⟩
  left_inv z := rfl
  right_inv y := by
    obtain ⟨z, hz, hy⟩ := (mem_sourceOrbit U H o y.1).mp y.2
    apply Subtype.ext
    change Sum.inr ((Sum.getRight? y.1).getD o.out) = y.1
    rw [hy]
    rfl

@[simp] theorem sourceOrbitEquiv_apply (o : Orbit (source U H)) (z : o.orbit) :
    ((sourceOrbitEquiv U H o z : (sourceOrbit U H o).orbit) : Ω ⊕ Z) =
      Sum.inr (z : Z) := rfl

/-- The actual image on the model orbit is the relabelled actual image on
the source orbit. -/
theorem relabel_orbitImage_sourceOrbit (o : Orbit (source U H)) :
    relabelSubgroup (sourceOrbitEquiv U H o) (orbitImage (source U H) o) =
      orbitImage (model U H) (sourceOrbit U H o) := by
  let eo := sourceOrbitEquiv U H o
  ext p
  constructor
  · intro hp
    rw [mem_relabelSubgroup] at hp
    obtain ⟨⟨σ, h, hh, rfl⟩, hσ⟩ := hp
    refine ⟨⟨fusionOrbitAction U h, h, hh, rfl⟩, ?_⟩
    apply Equiv.ext
    intro y
    obtain ⟨z, rfl⟩ := eo.surjective y
    have hz : (eo.symm.permCongr p) z =
        MulAction.toPermHom (source U H) o.orbit ⟨h.2, h, hh, rfl⟩ z :=
      (congrArg (fun f : Equiv.Perm o.orbit => f z) hσ).symm
    apply Subtype.ext
    have hp' : p (eo z) = eo ((eo.symm.permCongr p) z) := by
      simp [Equiv.permCongr_apply]
    rw [hp', hz]
    rfl
  · rintro ⟨⟨k, h, hh, rfl⟩, rfl⟩
    rw [mem_relabelSubgroup]
    refine ⟨⟨h.2, h, hh, rfl⟩, ?_⟩
    apply Equiv.ext
    intro z
    apply Subtype.ext
    change ((eo.symm (MulAction.toPermHom (model U H)
      (sourceOrbit U H o).orbit ⟨fusionOrbitAction U h, h, hh, rfl⟩ (eo z)) :
        o.orbit) : Z) = h.2 z
    have hy : (MulAction.toPermHom (model U H) (sourceOrbit U H o).orbit
        ⟨fusionOrbitAction U h, h, hh, rfl⟩ (eo z)) = eo ⟨h.2 z, by
          have hmem := (MulAction.toPermHom (model U H) (sourceOrbit U H o).orbit
            ⟨fusionOrbitAction U h, h, hh, rfl⟩ (eo z)).2
          exact (inr_mem_sourceOrbit U H o (h.2 z)).mp hmem⟩ := by
      apply Subtype.ext
      rfl
    rw [hy, Equiv.symm_apply_apply]

theorem sourceOrbit_injective : Function.Injective (sourceOrbit U H) := by
  intro o₁ o₂ he
  have hx : o₁.out ∈ o₁.orbit :=
    (MulAction.orbitRel.Quotient.mem_orbit).mpr (Quotient.out_eq' o₁)
  have hy : Sum.inr o₁.out ∈ (sourceOrbit U H o₂).orbit := by
    rw [← he, inr_mem_sourceOrbit]
    exact hx
  rw [inr_mem_sourceOrbit] at hy
  exact ((MulAction.orbitRel.Quotient.mem_orbit).mp hx).symm.trans
    ((MulAction.orbitRel.Quotient.mem_orbit).mp hy)

/-- A model orbit through a complement point is a source orbit. -/
theorem eq_sourceOrbit_of_inr (e : Orbit (model U H)) (z : Z)
    (hz : Sum.inr z ∈ e.orbit) :
    e = sourceOrbit U H (Quotient.mk'' z) := by
  have hz' : Sum.inr z ∈ (sourceOrbit U H (Quotient.mk'' z)).orbit := by
    rw [inr_mem_sourceOrbit]
    exact (MulAction.orbitRel.Quotient.mem_orbit).mpr rfl
  exact ((MulAction.orbitRel.Quotient.mem_orbit).mp hz).symm.trans
    ((MulAction.orbitRel.Quotient.mem_orbit).mp hz')

/-- With full projection onto a transitive retained action, the orbit through
a retained point is all of `inl Ω`. -/
theorem retained_orbit_eq_range
    (htrans : ∀ x y : Ω, ∃ u : U, (u : Equiv.Perm Ω) x = y)
    (hfull : H.map (MonoidHom.fst U (Equiv.Perm Z)) = ⊤) (x : Ω) :
    MulAction.orbit (model U H) (Sum.inl x : Ω ⊕ Z) =
      Set.range (Sum.inl : Ω → Ω ⊕ Z) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x', rfl⟩ := mem_model_orbit_inl U H x y hy
    exact ⟨x', rfl⟩
  · rintro ⟨x', rfl⟩
    obtain ⟨u, hu⟩ := htrans x x'
    have hmem : u ∈ H.map (MonoidHom.fst U (Equiv.Perm Z)) := by
      rw [hfull]
      exact Subgroup.mem_top u
    obtain ⟨h, hh, hhu⟩ := hmem
    refine ⟨⟨fusionOrbitAction U h, h, hh, rfl⟩, ?_⟩
    change fusionOrbitAction U h (Sum.inl x) = Sum.inl x'
    rw [fusionOrbitAction_inl]
    change Sum.inl (((MonoidHom.fst U (Equiv.Perm Z)) h : Equiv.Perm Ω) x) = _
    rw [hhu, hu]

end FusionSourceOrbits

open OrbitProfileFromOrbits FusionSourceOrbits

/-- The exact c=1 source pattern of a complete fusion model is inherited by
its complete source projection, provided the retained orbit is not itself
of degree three. -/
theorem C1DegreeNineSourcePattern.fusionSource
    {Ω Z : Type} [Finite Ω] (U : Subgroup (Equiv.Perm Ω))
    (htrans : ∀ x y : Ω, ∃ u : U, (u : Equiv.Perm Ω) x = y)
    (hdegree : Nat.card Ω ≠ 3)
    (H : Subgroup (U × Equiv.Perm Z))
    (hfull : H.map (MonoidHom.fst U (Equiv.Perm Z)) = ⊤)
    (hpattern : C1DegreeNineSourcePattern (model U H)) :
    C1DegreeNineSourcePattern (source U H) := by
  obtain ⟨exceptional, hregular, hunique, hnoA4⟩ := hpattern
  have htransfer (o : Orbit (source U H)) :
      IsRegularC3Orbit (model U H) (sourceOrbit U H o) ↔
        IsRegularC3Orbit (source U H) o := by
    let eo := sourceOrbitEquiv U H o
    have himage := relabel_orbitImage_sourceOrbit U H o
    let g : orbitImage (source U H) o ≃*
        orbitImage (model U H) (sourceOrbit U H o) :=
      (eo.permCongrHom.subgroupMap (orbitImage (source U H) o)).trans
        (MulEquiv.subgroupCongr himage)
    constructor
    · rintro ⟨hcard, hp⟩
      exact ⟨(Nat.card_congr eo).trans hcard, hp.of_equiv g.symm⟩
    · rintro ⟨hcard, hp⟩
      exact ⟨(Nat.card_congr eo).symm.trans hcard, hp.of_equiv g⟩
  have hexceptional : ∃ z : Z, Sum.inr z ∈ exceptional.orbit := by
    have hout : exceptional.out ∈ exceptional.orbit :=
      (MulAction.orbitRel.Quotient.mem_orbit).mpr (Quotient.out_eq' exceptional)
    rcases hy : exceptional.out with x | z
    · exfalso
      have horbit : exceptional.orbit = Set.range Sum.inl := by
        rw [orbit_eq_out, hy]
        exact retained_orbit_eq_range U H htrans hfull x
      have hcard : Nat.card exceptional.orbit = Nat.card Ω := by
        rw [horbit]
        exact Nat.card_range_of_injective Sum.inl_injective
      exact hdegree (hcard.symm.trans hregular.1)
    · exact ⟨z, hy ▸ hout⟩
  obtain ⟨z, hz⟩ := hexceptional
  have he := eq_sourceOrbit_of_inr U H exceptional z hz
  refine ⟨Quotient.mk'' z, ?_, ?_, ?_⟩
  · rw [← htransfer, ← he]
    exact hregular
  · intro o ho
    apply sourceOrbit_injective U H
    rw [hunique _ ((htransfer o).mpr ho), he]
  · intro o hA4
    apply hnoA4 (sourceOrbit U H o)
    have h := TernaryHighEarlierOwner.naturalA4_relabel (sourceOrbitEquiv U H o)
      (orbitImage (source U H) o) hA4
    rwa [relabel_orbitImage_sourceOrbit] at h

/-- The same inheritance after the canonical physical relabelling by
`finSumFinEquiv`, as used by every width-canonical cell predicate. -/
theorem C1DegreeNineSourcePattern.fusionSource_fin
    {w b : ℕ} (U : Subgroup (Equiv.Perm (Fin w)))
    (htrans : ∀ x y : Fin w, ∃ u : U, (u : Equiv.Perm (Fin w)) x = y)
    (hdegree : w ≠ 3)
    (H : Subgroup (U × Equiv.Perm (Fin b)))
    (hfull : H.map (MonoidHom.fst U (Equiv.Perm (Fin b))) = ⊤)
    (hpattern : C1DegreeNineSourcePattern
      (relabelSubgroup (finSumFinEquiv : Fin w ⊕ Fin b ≃ Fin (w + b))
        (H.map (fusionOrbitAction U)))) :
    C1DegreeNineSourcePattern (H.map (MonoidHom.snd U (Equiv.Perm (Fin b)))) := by
  apply C1DegreeNineSourcePattern.fusionSource U htrans (by simpa using hdegree) H hfull
  exact (c1DegreeNineSourcePattern_relabel_iff _ _).mp hpattern

end SymmetricSubgroupAsymptotics

end
