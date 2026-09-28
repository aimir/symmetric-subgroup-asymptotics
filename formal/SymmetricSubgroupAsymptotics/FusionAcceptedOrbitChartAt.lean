import SymmetricSubgroupAsymptotics.FusionOrbitProfileChart

/-!
# Exact chart at a specified full fusion orbit

A full projection onto a transitive displayed action makes the displayed
block an actual orbit.  This version fixes the base point and therefore fixes
the quotient-orbit witness literally; later arguments can prove that this
orbit is disjoint from a selected complement orbit.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- The orbit of the specified displayed point has exactly the supplied
permutation action after its literal point chart. -/
theorem fusionAcceptedOrbit_physical_orbit_chart_at
    {Ω Z X : Type*} [Fintype Ω] [Fintype Z] [Fintype X]
    (U : Subgroup (Equiv.Perm Ω))
    (htrans : ∀ x y : Ω, ∃ u : U, (u : Equiv.Perm Ω) x = y)
    (q : Ω ⊕ Z ≃ X)
    (H : Subgroup (U × Equiv.Perm Z))
    (hfull : H.map (MonoidHom.fst U (Equiv.Perm Z)) = ⊤)
    (x : Ω) :
    let G := relabelSubgroup q (H.map (fusionOrbitAction U))
    let o : OrbitProfileFromOrbits.Orbit G := Quotient.mk'' (q (Sum.inl x))
    ∃ e : Ω ≃ o.orbit,
      relabelSubgroup e U = OrbitProfileFromOrbits.orbitImage G o := by
  let K := H.map (fusionOrbitAction U)
  let G := relabelSubgroup q K
  let z : X := q (Sum.inl x)
  let o : OrbitProfileFromOrbits.Orbit G := Quotient.mk'' z
  have hKorbit : MulAction.orbit K (Sum.inl x) =
      Set.range (Sum.inl : Ω → Ω ⊕ Z) :=
    fusionOrbitAction_orbit_eq U htrans ⟨H, hfull⟩ x
  have horbit : MulAction.orbit G z =
      Set.range (fun y : Ω => q (Sum.inl y)) := by
    ext a
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨k, hk, hkg⟩ := g.property
      have hmem : k (Sum.inl x) ∈ MulAction.orbit K (Sum.inl x) :=
        ⟨⟨k, hk⟩, rfl⟩
      rw [hKorbit] at hmem
      obtain ⟨y, hy⟩ := hmem
      refine ⟨y, ?_⟩
      have hgapp :
          (g : Equiv.Perm X) (q (Sum.inl x)) =
            q (k (Sum.inl x)) := by
        rw [← hkg]
        change q (k (q.symm (q (Sum.inl x)))) = q (k (Sum.inl x))
        rw [q.symm_apply_apply]
      exact (congrArg q hy).trans hgapp.symm
    · rintro ⟨y, rfl⟩
      have hmem : (Sum.inl y : Ω ⊕ Z) ∈
          MulAction.orbit K (Sum.inl x : Ω ⊕ Z) := by
        rw [hKorbit]
        exact ⟨y, rfl⟩
      obtain ⟨k, hk⟩ := hmem
      let g : G :=
        ⟨q.permCongr (k : Equiv.Perm (Ω ⊕ Z)),
          ⟨k, k.property, rfl⟩⟩
      refine ⟨g, ?_⟩
      change (g : Equiv.Perm X) z = q (Sum.inl y)
      dsimp only [g, z]
      change q ((k : Equiv.Perm (Ω ⊕ Z)) (q.symm (q (Sum.inl x)))) =
        q (Sum.inl y)
      rw [q.symm_apply_apply]
      exact congrArg q hk
  have hb : Set.range (fun y : Ω => q (Sum.inl y)) = o.orbit :=
    horbit.symm.trans (MulAction.orbitRel.Quotient.orbit_mk z).symm
  have hinj : Function.Injective (fun y : Ω => q (Sum.inl y)) := by
    intro y y' h
    exact Sum.inl_injective (q.injective h)
  let e : Ω ≃ o.orbit :=
    (Equiv.ofInjective (fun y : Ω => q (Sum.inl y)) hinj).trans
      (Equiv.setCongr hb)
  have he (y : Ω) : (e y : X) = q (Sum.inl y) := rfl
  have htransport (g : G) (u : U)
      (hu : ∀ y : Ω,
        (g : Equiv.Perm X) (q (Sum.inl y)) =
          q (Sum.inl ((u : Equiv.Perm Ω) y))) :
      e.permCongr (u : Equiv.Perm Ω) =
        MulAction.toPermHom G o.orbit g := by
    apply Equiv.ext
    intro a
    apply Subtype.ext
    change (e ((u : Equiv.Perm Ω) (e.symm a)) : X) =
      (g : Equiv.Perm X) (a : X)
    rw [he, ← hu]
    have ha : q (Sum.inl (e.symm a)) = (a : X) :=
      congrArg Subtype.val (e.apply_symm_apply a)
    exact congrArg (g : Equiv.Perm X) ha
  refine ⟨e, ?_⟩
  ext v
  change v ∈ U.map e.permCongrHom.toMonoidHom ↔
    v ∈ (MulAction.toPermHom G o.orbit).range
  constructor
  · rintro ⟨u, hu, rfl⟩
    let u₀ : U := ⟨u, hu⟩
    have hm : u₀ ∈ H.map (MonoidHom.fst U (Equiv.Perm Z)) := by
      rw [hfull]
      trivial
    obtain ⟨p, hp, hpu⟩ := hm
    let g : G :=
      ⟨q.permCongr (fusionOrbitAction U p),
        ⟨fusionOrbitAction U p, ⟨p, hp, rfl⟩, rfl⟩⟩
    refine ⟨g, (htransport g u₀ ?_).symm⟩
    intro y
    change (q.permCongr (fusionOrbitAction U p)) (q (Sum.inl y)) =
      q (Sum.inl ((u₀ : Equiv.Perm Ω) y))
    change q ((fusionOrbitAction U p) (q.symm (q (Sum.inl y)))) = _
    rw [q.symm_apply_apply]
    change q (Sum.inl ((p.1 : Equiv.Perm Ω) y)) =
      q (Sum.inl ((u₀ : Equiv.Perm Ω) y))
    have hpu' : (p.1 : Equiv.Perm Ω) = (u₀ : Equiv.Perm Ω) :=
      congrArg Subtype.val hpu
    rw [hpu']
  · rintro ⟨g, rfl⟩
    obtain ⟨k, hk, hkg⟩ := g.property
    obtain ⟨p, hp, hpk⟩ := hk
    let u : U := p.1
    refine ⟨u, u.property, htransport g u ?_⟩
    intro y
    have hgapp :
        (g : Equiv.Perm X) (q (Sum.inl y)) =
          q (k (Sum.inl y)) := by
      rw [← hkg]
      change q (k (q.symm (q (Sum.inl y)))) = q (k (Sum.inl y))
      rw [q.symm_apply_apply]
    calc
      (g : Equiv.Perm X) (q (Sum.inl y)) = q (k (Sum.inl y)) := hgapp
      _ = q (fusionOrbitAction U p (Sum.inl y)) := by rw [← hpk]
      _ = q (Sum.inl ((u : Equiv.Perm Ω) y)) := rfl

end SymmetricSubgroupAsymptotics

end
