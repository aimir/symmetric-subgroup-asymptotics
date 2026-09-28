import SymmetricSubgroupAsymptotics.C3CompletePhysicalContinuation
import SymmetricSubgroupAsymptotics.Non2OutsideFrontierAdapter
import SymmetricSubgroupAsymptotics.OutsideOrbitTernaryChart

/-!
# The complete regular-C3 audit lies in the general non-2 frontier

Full projection onto a transitive fusion action makes the marked physical
block an actual orbit, even after an arbitrary relabelling of the whole point
set.  Applied to the regular C3 action, that orbit has image of order three,
so it is neither binary nor the full degree-three marker action.  Hence the
complete regular-C3 ordinary family is a literal subfamily of the general
outside-`Fits` frontier.  Any complete general non-2 forward estimate therefore
closes the c=1 audit directly; the finite owner continuation remains an
independent branch-by-branch check.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A full local fusion projection becomes an actual orbit with exactly the
specified action after any relabelling of the complete physical point set. -/
theorem fusionAcceptedOrbit_physical_orbit_chart
    {Ω Z X : Type*} [Fintype Ω] [Fintype Z] [Fintype X] [Nonempty Ω]
    (U : Subgroup (Equiv.Perm Ω))
    (htrans : ∀ x y : Ω, ∃ u : U, (u : Equiv.Perm Ω) x = y)
    (q : Ω ⊕ Z ≃ X)
    (H : Subgroup (U × Equiv.Perm Z))
    (hfull : H.map (MonoidHom.fst U (Equiv.Perm Z)) = ⊤) :
    ∃ o : OrbitProfileFromOrbits.Orbit
        (relabelSubgroup q (H.map (fusionOrbitAction U))),
      ∃ e : Ω ≃ o.orbit,
        relabelSubgroup e U =
          OrbitProfileFromOrbits.orbitImage
            (relabelSubgroup q (H.map (fusionOrbitAction U))) o := by
  let K := H.map (fusionOrbitAction U)
  let G := relabelSubgroup q K
  let x : Ω := Classical.choice (inferInstance : Nonempty Ω)
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
  refine ⟨o, e, ?_⟩
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

theorem ternaryRegularAction_not_isPGroup_two :
    ¬ IsPGroup 2 ternaryRegularAction := by
  intro h
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h
  rw [ternaryRegularAction_card] at hk
  cases k with
  | zero => norm_num at hk
  | succ k =>
      rw [pow_succ] at hk
      omega

/-- A complete regular-C3 physical subgroup is outside the repeated-marker
alphabet: its distinguished orbit is cyclic of order three, while the only
allowed degree-three marker image is the full symmetric group. -/
theorem c3CompleteOrdinaryPhysical_mem_outsideFits
    (b : ℕ) (G : Subgroup (Equiv.Perm (Fin (3+b))))
    (hG : G ∈ C3CompleteOrdinaryPhysicalSet b) :
    G ∈ RepeatedMarkerOwnerBound.OutsideFitsSubgroupSetAt (3+b) := by
  obtain ⟨⟨K, hK⟩, rfl⟩ := hG
  obtain ⟨⟨s, ⟨M, hM⟩⟩, rfl⟩ := hK
  obtain ⟨H, hAccepted, rfl⟩ := hM
  let K₀ := H.1.map (fusionOrbitAction ternaryRegularAction)
  let t : Equiv.Perm (Fin (3+b)) :=
    (c3ResidualPointEquiv b).symm.trans
      (s.trans (c3ResidualPointEquiv b))
  have ht : (c3ResidualPointEquiv b).trans t =
      s.trans (c3ResidualPointEquiv b) := by
    ext x
    simp only [t, Equiv.trans_apply, Equiv.symm_apply_apply]
  have hphysical :
      relabelSubgroup (c3ResidualPointEquiv b)
          (relabelSubgroup s K₀) =
        relabelSubgroup t
          (relabelSubgroup (c3ResidualPointEquiv b) K₀) := by
    simp only [relabelSubgroup_trans, ht]
  have hnoncritical₀ :
      ¬ IsCriticalSubgroup (3+b)
        (relabelSubgroup (c3ResidualPointEquiv b) K₀) := H.2.2
  have hnoncritical :
      ¬ IsCriticalSubgroup (3+b)
        (relabelSubgroup (c3ResidualPointEquiv b)
          (relabelSubgroup s K₀)) := by
    rw [hphysical]
    exact (ordinaryRemainder_relabel_iff (3+b) t _).mpr hnoncritical₀
  refine ⟨hnoncritical, ?_⟩
  intro hFits
  obtain ⟨o, e, himage⟩ := fusionAcceptedOrbit_physical_orbit_chart
    ternaryRegularAction
    (fun x y => by
      obtain ⟨g, hg⟩ := ternaryRegularAction_transitive x y
      exact ⟨g, hg⟩)
    (s.trans (c3ResidualPointEquiv b)) H.1 H.2.1
  have hcardImage :
      Nat.card (OrbitProfileFromOrbits.orbitImage
        (relabelSubgroup (s.trans (c3ResidualPointEquiv b)) K₀) o) = 3 := by
    rw [← himage]
    change Nat.card (ternaryRegularAction.map e.permCongrHom.toMonoidHom) = 3
    rw [Subgroup.card_map_of_injective e.permCongrHom.injective,
      ternaryRegularAction_card]
  have hFits' : RepeatedMarkerOrbitProfiles.Fits
      (relabelSubgroup (s.trans (c3ResidualPointEquiv b)) K₀) := by
    simpa only [relabelSubgroup_trans] using hFits
  rcases hFits' o with hbinary | ⟨d, hd⟩
  · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hbinary
    rw [hcardImage] at hk
    cases k with
    | zero => norm_num at hk
    | succ k =>
        rw [pow_succ] at hk
        omega
  · have hmarkerCard :
        Nat.card (relabelSubgroup d oddMarkerActionSubgroup) = 6 := by
      change Nat.card
        (oddMarkerActionSubgroup.map
          d.permCongrHom.toMonoidHom) = 6
      rw [Subgroup.card_map_of_injective d.permCongrHom.injective]
      norm_num [oddMarkerActionSubgroup,
        Nat.card_eq_fintype_card, Fintype.card_perm]
    have hc : Nat.card (relabelSubgroup d oddMarkerActionSubgroup) = 3 := by
      rw [hd]
      exact hcardImage
    rw [hmarkerCard] at hc
    omega

theorem c3CompleteOrdinaryPhysical_card_le_outsideFits (b : ℕ) :
    Nat.card (C3CompleteOrdinaryPhysicalSet b) ≤
      Nat.card (RepeatedMarkerOwnerBound.OutsideFitsSubgroupSetAt (3+b)) :=
  Nat.card_le_card_of_injective
    (fun G : C3CompleteOrdinaryPhysicalSet b =>
      (⟨G.1, c3CompleteOrdinaryPhysical_mem_outsideFits b G.1 G.2⟩ :
        RepeatedMarkerOwnerBound.OutsideFitsSubgroupSetAt (3+b)))
    (fun G G' h => by
      apply Subtype.ext
      exact congrArg
        (fun z : RepeatedMarkerOwnerBound.OutsideFitsSubgroupSetAt (3+b) => z.1) h)

/-- The complete regular-C3 ratio is pointwise dominated by the general
non-2 outside frontier, in every ambient degree. -/
theorem c3CompleteOrdinaryRatio_le_outsideFrontierRatio (n : ℕ) :
    c3CompleteOrdinaryRatio n ≤
      OrdinaryFrontierClosure.outsideFrontierRatio n := by
  rw [RepeatedMarkerOwnerBound.outsideFrontierRatio_eq_outsideFitsAtRatio]
  by_cases hn : 3 ≤ n
  · obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hsub : 3 + b - 3 = b := by omega
    have hcard := c3CompleteOrdinaryPhysical_card_le_outsideFits b
    unfold c3CompleteOrdinaryRatio
      RepeatedMarkerOwnerBound.outsideFitsAtRatio
    rw [if_pos (by omega), hsub]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcard)
      (exactBenchmark_pos (3+b)).le
  · unfold c3CompleteOrdinaryRatio
      RepeatedMarkerOwnerBound.outsideFitsAtRatio
    rw [if_neg hn]
    exact div_nonneg (Nat.cast_nonneg _) (exactBenchmark_pos n).le

/-- The reusable general non-2 estimate closes the complete c=1 audit by
pointwise inclusion, with no extra c=1 numerical hypothesis. -/
noncomputable def c3CompleteOrdinary_exponentialForwardEstimate_of_outside
    (E : OrdinaryFrontierClosure.ExponentialForwardEstimate
      OrdinaryFrontierClosure.outsideFrontierRatio) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      c3CompleteOrdinaryRatio :=
  OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le E 0
    (fun n _ => c3CompleteOrdinaryRatio_le_outsideFrontierRatio n)

end SymmetricSubgroupAsymptotics

end
