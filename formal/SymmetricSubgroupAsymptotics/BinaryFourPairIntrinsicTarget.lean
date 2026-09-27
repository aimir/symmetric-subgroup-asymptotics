import SymmetricSubgroupAsymptotics.BinaryFourPairHallIncidence
import SymmetricSubgroupAsymptotics.OrbitProfileSelectedOrbit
import SymmetricSubgroupAsymptotics.CriticalOrbitCriterion
import SymmetricSubgroupAsymptotics.FiniteProductPGroup

/-!
# Intrinsic ownership of the selected four-pair profiles

The finite-menu Hall theorem is useful only after its target profiles are
returned to the intrinsic noncritical binary family.  A profile is selected
when one occupied residual colour is not one of the four critical original
actions.  The occurrence itself supplies the actual noncritical orbit.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryFourPairIntrinsicTarget

open BinaryFourPairHallIncidence

/-- A residual menu colour is genuinely outside the four critical original
permutation actions. -/
def IsNoncriticalResidual (N : ℕ) (a : BinaryResidualOrbitMenu.Label (2*N)) : Prop :=
  ¬ ∃ i : CriticalActionKind,
    ∃ e : criticalActionPoints i ≃ BinaryResidualOrbitMenu.points (2*N) a,
      relabelSubgroup e (criticalActionSubgroup i) =
        BinaryResidualOrbitMenu.action (2*N) a

/-- A common Hall profile retains at least one occupied noncritical colour. -/
def HasNoncriticalResidual (N : ℕ) (t : ResidualProfile N) : Prop :=
  ∃ a : BinaryResidualOrbitMenu.Label (2*N),
    IsNoncriticalResidual N a ∧ 0 < t.2 a

theorem criticalAction_isPGroup (i : CriticalActionKind) :
    IsPGroup 2 (criticalActionSubgroup i) := by
  cases i with
  | c2 => exact IsPGroup.of_card (n := 1) (by
      simpa [criticalActionOrder] using criticalAction_group_card .c2)
  | v4 => exact IsPGroup.of_card (n := 2) (by
      simpa [criticalActionOrder] using criticalAction_group_card .v4)
  | d8 => exact IsPGroup.of_card (n := 3) (by
      simpa [criticalActionOrder] using criticalAction_group_card .d8)
  | e8 => exact IsPGroup.of_card (n := 5) (by
      simpa [criticalActionOrder] using criticalAction_group_card .e8)

abbrev FullIndex (N : ℕ) :=
  PUnit.{1} ⊕ BinaryPairE8Profile.ExteriorIndex
    (α := BinaryResidualOrbitMenu.Label (2*N))

theorem fullAction_isPGroup (N : ℕ) (i : FullIndex N) :
    IsPGroup 2 (BinaryFourPairProfileUnion.FullAction
      (BinaryResidualOrbitMenu.points (2*N))
      (BinaryResidualOrbitMenu.action (2*N)) i) := by
  cases i with
  | inl i => exact criticalAction_isPGroup .c2
  | inr i =>
    cases i with
    | inl i => exact criticalAction_isPGroup .e8
    | inr a => exact BinaryResidualOrbitMenu.action_isPGroup (2*N) a

theorem fullAction_transitive (N : ℕ) (i : FullIndex N)
    (x y : BinaryFourPairProfileUnion.FullPoints
      (BinaryResidualOrbitMenu.points (2*N)) i) :
    ∃ u : BinaryFourPairProfileUnion.FullAction
        (BinaryResidualOrbitMenu.points (2*N))
        (BinaryResidualOrbitMenu.action (2*N)) i,
      (u : Equiv.Perm (BinaryFourPairProfileUnion.FullPoints
        (BinaryResidualOrbitMenu.points (2*N)) i)) x = y := by
  cases i with
  | inl i => exact criticalAction_transitive .c2 x y
  | inr i =>
    cases i with
    | inl i => exact criticalAction_transitive .e8 x y
    | inr a => exact BinaryResidualOrbitMenu.action_transitive (2*N) a x y

theorem fullAction_moves_point (N : ℕ) (i : FullIndex N)
    (x : BinaryFourPairProfileUnion.FullPoints
      (BinaryResidualOrbitMenu.points (2*N)) i) :
    ∃ u : BinaryFourPairProfileUnion.FullAction
        (BinaryResidualOrbitMenu.points (2*N))
        (BinaryResidualOrbitMenu.action (2*N)) i,
      (u : Equiv.Perm (BinaryFourPairProfileUnion.FullPoints
        (BinaryResidualOrbitMenu.points (2*N)) i)) x ≠ x := by
  cases i with
  | inl i => exact criticalAction_moves_point .c2 x
  | inr i =>
    cases i with
    | inl i => exact criticalAction_moves_point .e8 x
    | inr a =>
      change BinaryResidualOrbitMenu.points (2*N) a at x
      change ∃ u : BinaryResidualOrbitMenu.action (2*N) a,
        (u : Equiv.Perm (BinaryResidualOrbitMenu.points (2*N) a)) x ≠ x
      have hcard : 1 < Fintype.card (BinaryResidualOrbitMenu.points (2*N) a) := by
        exact lt_trans (by decide : 1 < 2) a.1.2
      letI : Nontrivial (BinaryResidualOrbitMenu.points (2*N) a) :=
        Fintype.one_lt_card_iff_nontrivial.mp hcard
      obtain ⟨y,hy⟩ := exists_ne x
      obtain ⟨u,hu⟩ := BinaryResidualOrbitMenu.action_transitive (2*N) a x y
      exact ⟨u,by rwa [hu]⟩

/-- Fullness inside a product of p-group orbit actions makes the literal
permutation subgroup a p-group. -/
theorem fullProfile_isPGroup {p : ℕ} {ι : Type*} [Fintype ι]
    {Ω : ι → Type*} {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {K : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m))}
    (hU : ∀ i, IsPGroup p (U i)) (hK : OrbitProfileFull U 1 K) :
    IsPGroup p K := by
  intro g
  obtain ⟨d,hd⟩ := orbitProfileFull_le_product_range hK g.2
  obtain ⟨n,hn⟩ := orbitProfileProduct_isPGroup m U hU d
  refine ⟨n,Subtype.ext ?_⟩
  change g.val ^ (p^n) = 1
  rw [← hd, ← map_pow, hn, map_one]

theorem fullOn_isFixedPointFreeBinary (N : ℕ) {m : FullIndex N → ℕ}
    {e : OrbitProfilePoints
      (BinaryFourPairProfileUnion.FullPoints
        (BinaryResidualOrbitMenu.points (2*N))) m ≃ Fin (2*N)}
    {H : Subgroup (Equiv.Perm (Fin (2*N)))}
    (hH : OrbitProfileFullOn
      (BinaryFourPairProfileUnion.FullAction
        (BinaryResidualOrbitMenu.points (2*N))
        (BinaryResidualOrbitMenu.action (2*N))) e H) :
    IsFixedPointFreeBinary H := by
  constructor
  · let K := relabelSubgroup e.symm H
    have hKOn : OrbitProfileFullOn
        (BinaryFourPairProfileUnion.FullAction
          (BinaryResidualOrbitMenu.points (2*N))
          (BinaryResidualOrbitMenu.action (2*N)))
        (Equiv.refl _) K := by
      simpa only [Equiv.self_trans_symm] using hH.relabel e.symm
    have hK : OrbitProfileFull
        (BinaryFourPairProfileUnion.FullAction
          (BinaryResidualOrbitMenu.points (2*N))
          (BinaryResidualOrbitMenu.action (2*N))) 1 K :=
      (orbitProfileFullOn_iff _ _ _).mp hKOn
    have hpK : IsPGroup 2 K := fullProfile_isPGroup
      (fun i => fullAction_isPGroup N i) hK
    have hp := hpK.map e.permCongrHom.toMonoidHom
    change IsPGroup 2 (relabelSubgroup e K) at hp
    have heq : relabelSubgroup e K = H := by
      dsimp only [K]
      exact relabelSubgroup_symm e.symm H
    rwa [heq] at hp
  · exact hH.hasNoFixedPoints (fullAction_moves_point N)

/-- An occupied noncritical residual occurrence is an actual noncritical
orbit, so the represented physical subgroup cannot enter the critical owner. -/
theorem fullOn_not_evenCritical (N : ℕ) (t : ResidualProfile N)
    (ht : HasNoncriticalResidual N t)
    (q r : ℕ)
    {e : OrbitProfilePoints
      (BinaryFourPairProfileUnion.FullPoints
        (BinaryResidualOrbitMenu.points (2*N)))
      (RepeatedMarkerMergedProfile.multiplicity
        (BinaryPairE8Profile.exteriorMultiplicity t.2 r) q) ≃ Fin (2*N)}
    {H : Subgroup (Equiv.Perm (Fin (2*N)))}
    (hH : OrbitProfileFullOn
      (BinaryFourPairProfileUnion.FullAction
        (BinaryResidualOrbitMenu.points (2*N))
        (BinaryResidualOrbitMenu.action (2*N))) e H) :
    ¬ IsEvenCriticalSubgroup N H := by
  obtain ⟨a,ha,hpos⟩ := ht
  let j : Fin (t.2 a) := ⟨0,hpos⟩
  let x : BinaryResidualOrbitMenu.points (2*N) a := Classical.choice inferInstance
  obtain ⟨o,c,hc⟩ := hH.selected_orbit_image (fullAction_transitive N)
    (.inr (.inr a)) j x
  intro hcritical
  have hall := (CriticalOrbitCriterion.isEvenCritical_iff N H).mp hcritical o
  obtain ⟨i,d,hd⟩ := hall
  apply ha
  refine ⟨i,d.trans c.symm,?_⟩
  calc
    relabelSubgroup (d.trans c.symm) (criticalActionSubgroup i) =
        relabelSubgroup c.symm
          (relabelSubgroup d (criticalActionSubgroup i)) :=
      (relabelSubgroup_trans d c.symm _).symm
    _ = relabelSubgroup c.symm
          (OrbitProfileFromOrbits.orbitImage H o) := by rw [hd]
    _ = BinaryResidualOrbitMenu.action (2*N) a := by
      rw [← hc]
      exact relabelSubgroup_symm c _

theorem sourceSelected_isNoncritical (N : ℕ) (S : Finset (ResidualProfile N))
    (hselected : ∀ t ∈ S, HasNoncriticalResidual N t)
    (H : SourceFamily N S) :
    IsFixedPointFreeBinary H.val ∧ ¬ IsEvenCriticalSubgroup N H.val := by
  obtain ⟨t,e,K,hK,hKH⟩ := H.property
  have h0 : OrbitProfileFullOn
      (BinaryFourPairProfileUnion.FullAction
        (BinaryResidualOrbitMenu.points (2*N))
        (BinaryResidualOrbitMenu.action (2*N))) (Equiv.refl _) K :=
    (orbitProfileFullOn_iff _ _ _).mpr hK
  have hOn : OrbitProfileFullOn
      (BinaryFourPairProfileUnion.FullAction
        (BinaryResidualOrbitMenu.points (2*N))
        (BinaryResidualOrbitMenu.action (2*N))) e H.val := by
    rw [← hKH]
    simpa only [Equiv.refl_trans] using h0.relabel e
  exact ⟨fullOn_isFixedPointFreeBinary N hOn,
    fullOn_not_evenCritical N t.val (hselected t.val t.property)
      (t.val.1.1+4) t.val.1.2 hOn⟩

theorem targetSelected_isNoncritical (N : ℕ) (S : Finset (ResidualProfile N))
    (hselected : ∀ t ∈ S, HasNoncriticalResidual N t)
    (H : TargetFamily N S) :
    IsFixedPointFreeBinary H.val ∧ ¬ IsEvenCriticalSubgroup N H.val := by
  obtain ⟨t,e,K,hK,hKH⟩ := H.property
  have h0 : OrbitProfileFullOn
      (BinaryFourPairProfileUnion.FullAction
        (BinaryResidualOrbitMenu.points (2*N))
        (BinaryResidualOrbitMenu.action (2*N))) (Equiv.refl _) K :=
    (orbitProfileFullOn_iff _ _ _).mpr hK
  have hOn : OrbitProfileFullOn
      (BinaryFourPairProfileUnion.FullAction
        (BinaryResidualOrbitMenu.points (2*N))
        (BinaryResidualOrbitMenu.action (2*N))) e H.val := by
    rw [← hKH]
    simpa only [Equiv.refl_trans] using h0.relabel e
  exact ⟨fullOn_isFixedPointFreeBinary N hOn,
    fullOn_not_evenCritical N t.val (hselected t.val t.property)
      t.val.1.1 (t.val.1.2+1) hOn⟩

def sourceEmbedding (N : ℕ) (S : Finset (ResidualProfile N))
    (hselected : ∀ t ∈ S, HasNoncriticalResidual N t) :
    SourceFamily N S ↪ NoncriticalBinarySubgroups N where
  toFun H := ⟨H.val,sourceSelected_isNoncritical N S hselected H⟩
  inj' := by
    intro H K h
    exact Subtype.ext (congrArg (fun L : NoncriticalBinarySubgroups N => L.val) h)

def targetEmbedding (N : ℕ) (S : Finset (ResidualProfile N))
    (hselected : ∀ t ∈ S, HasNoncriticalResidual N t) :
    TargetFamily N S ↪ NoncriticalBinarySubgroups N where
  toFun H := ⟨H.val,targetSelected_isNoncritical N S hselected H⟩
  inj' := by
    intro H K h
    exact Subtype.ext (congrArg (fun L : NoncriticalBinarySubgroups N => L.val) h)

theorem source_card_le_noncritical (N : ℕ) (S : Finset (ResidualProfile N))
    (hselected : ∀ t ∈ S, HasNoncriticalResidual N t) :
    Nat.card (SourceFamily N S) ≤ Nat.card (NoncriticalBinarySubgroups N) :=
  Nat.card_le_card_of_injective _ (sourceEmbedding N S hselected).injective

theorem target_card_le_noncritical (N : ℕ) (S : Finset (ResidualProfile N))
    (hselected : ∀ t ∈ S, HasNoncriticalResidual N t) :
    Nat.card (TargetFamily N S) ≤ Nat.card (NoncriticalBinarySubgroups N) :=
  Nat.card_le_card_of_injective _ (targetEmbedding N S hselected).injective

end SymmetricSubgroupAsymptotics.BinaryFourPairIntrinsicTarget

end
