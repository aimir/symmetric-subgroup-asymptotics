import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFiniteNormalImporter
import SymmetricSubgroupAsymptotics.FiniteTwoNormalSocleGenerators
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Quotient socles from a complete finite normal registry

For a fixed normal subgroup `N`, the minimal normal subgroups of `G / N`
correspond exactly to the normal subgroups of `G` which are minimal strictly
above `N`.  This file packages the finite certificate needed by catalogue
emitters: list those relative atoms, identify their supremum, and give one
element whose normal closure modulo `N` is that supremum.

The resulting theorem produces `SocleNormalGeneratorBound (G ⨸ N) 1`.
All completeness reasoning is semantic; a generated row proves the finite
state conditions using its checked complete normal registry.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A normal subgroup minimal among those strictly above `N`. -/
def IsMinimalNormalAbove {G : Type} [Group G]
    (N M : Subgroup G) : Prop :=
  M.Normal ∧ N < M ∧
    ∀ K : Subgroup G, K.Normal → N < K → K ≤ M → K = M

namespace IsMinimalNormalAbove

variable {G : Type} [Group G] {N M : Subgroup G} [N.Normal]

/-- A relative minimal normal subgroup maps to a minimal normal subgroup of
the quotient. -/
theorem map_quotient (h : IsMinimalNormalAbove N M) :
    IsMinimalNormalSubgroup (M.map (QuotientGroup.mk' N)) := by
  have hNM : N ≤ M := h.2.1.le
  refine ⟨h.1.map _ (QuotientGroup.mk'_surjective N), ?_, ?_⟩
  · intro hbot
    apply h.2.1.ne
    apply le_antisymm hNM
    have hc := congrArg
      (Subgroup.comap (QuotientGroup.mk' N)) hbot
    simpa only [QuotientGroup.comap_map_mk', sup_eq_right.mpr hNM,
      MonoidHom.comap_bot, QuotientGroup.ker_mk'] using hc
  · intro L hL hLne hLM
    let K : Subgroup G := L.comap (QuotientGroup.mk' N)
    have hKN : N ≤ K := QuotientGroup.le_comap_mk' N L
    have hKne : K ≠ N := by
      intro hKN_eq
      apply hLne
      calc
        L = K.map (QuotientGroup.mk' N) :=
          (Subgroup.map_comap_eq_self_of_surjective
            (QuotientGroup.mk'_surjective N) L).symm
        _ = N.map (QuotientGroup.mk' N) := by rw [hKN_eq]
        _ = ⊥ := QuotientGroup.map_mk'_self N
    have hKM : K ≤ M := by
      have hc := Subgroup.comap_mono (f := QuotientGroup.mk' N) hLM
      simpa only [K, QuotientGroup.comap_map_mk',
        sup_eq_right.mpr hNM] using hc
    have hKeq : K = M := h.2.2 K
      (hL.comap (QuotientGroup.mk' N))
      (lt_of_le_of_ne hKN (Ne.symm hKne)) hKM
    calc
      L = K.map (QuotientGroup.mk' N) :=
        (Subgroup.map_comap_eq_self_of_surjective
          (QuotientGroup.mk'_surjective N) L).symm
      _ = M.map (QuotientGroup.mk' N) := by rw [hKeq]

/-- The preimage of a quotient minimal normal subgroup is minimal strictly
above the quotient kernel. -/
theorem comap_quotient
    (L : Subgroup (G ⨸ N)) (hL : IsMinimalNormalSubgroup L) :
    IsMinimalNormalAbove N (L.comap (QuotientGroup.mk' N)) := by
  let M : Subgroup G := L.comap (QuotientGroup.mk' N)
  have hNM : N ≤ M := QuotientGroup.le_comap_mk' N L
  have hMne : M ≠ N := by
    intro hMN
    apply hL.2.1
    calc
      L = M.map (QuotientGroup.mk' N) :=
        (Subgroup.map_comap_eq_self_of_surjective
          (QuotientGroup.mk'_surjective N) L).symm
      _ = N.map (QuotientGroup.mk' N) := by rw [hMN]
      _ = ⊥ := QuotientGroup.map_mk'_self N
  refine ⟨hL.1.comap (QuotientGroup.mk' N),
    lt_of_le_of_ne hNM (Ne.symm hMne), ?_⟩
  intro K hK hNK hKM
  have hmapNormal : (K.map (QuotientGroup.mk' N)).Normal :=
    hK.map _ (QuotientGroup.mk'_surjective N)
  have hmapNe : K.map (QuotientGroup.mk' N) ≠ ⊥ := by
    intro hbot
    have hc := congrArg
      (Subgroup.comap (QuotientGroup.mk' N)) hbot
    have hKN : N ≤ K := hNK.le
    have : K = N := by
      simpa only [QuotientGroup.comap_map_mk',
        sup_eq_right.mpr hKN, MonoidHom.comap_bot,
        QuotientGroup.ker_mk'] using hc
    exact hNK.ne this.symm
  have hmapLe : K.map (QuotientGroup.mk' N) ≤ L := by
    rw [Subgroup.map_le_iff_le_comap]
    exact hKM
  have hmapEq := hL.2.2 (K.map (QuotientGroup.mk' N))
    hmapNormal hmapNe hmapLe
  calc
    K = (K.map (QuotientGroup.mk' N)).comap
          (QuotientGroup.mk' N) := by
      rw [QuotientGroup.comap_map_mk', sup_eq_right.mpr hNK.le]
    _ = L.comap (QuotientGroup.mk' N) := by rw [hmapEq]

/-- Relative minimality is invariant under a group equivalence. -/
theorem map_equiv {H : Type} [Group H]
    (h : IsMinimalNormalAbove N M) (e : G ≃* H) :
    IsMinimalNormalAbove (e.mapSubgroup N) (e.mapSubgroup M) := by
  let E : Subgroup G ≃o Subgroup H := e.mapSubgroup
  refine ⟨h.1.map e.toMonoidHom e.surjective,
    E.lt_iff_lt.2 h.2.1, ?_⟩
  intro K hK hNK hKM
  let L : Subgroup G := E.symm K
  have hNL : N < L := by
    apply E.lt_iff_lt.mp
    simpa only [L, E.apply_symm_apply] using hNK
  have hLM : L ≤ M := by
    apply E.le_iff_le.mp
    simpa only [L, E.apply_symm_apply] using hKM
  have hLNormal : L.Normal := by
    have hback := hK.map e.symm.toMonoidHom e.symm.surjective
    change (E.symm K).Normal at hback
    exact hback
  have hLeq : L = M := h.2.2 L hLNormal hNL hLM
  calc
    K = E L := (E.apply_symm_apply K).symm
    _ = E M := by rw [hLeq]

end IsMinimalNormalAbove

/-- Finite, checkable data identifying and normally generating the full
socle above one quotient kernel. -/
structure FiniteRelativeSocleGeneratorData
    (G : Type) [Group G] (N : Subgroup G) : Type 1 where
  base_normal : N.Normal
  Component : Type
  [component_fintype : Fintype Component]
  component : Component → Subgroup G
  component_minimal : ∀ i, IsMinimalNormalAbove N (component i)
  component_complete : ∀ M : Subgroup G,
    IsMinimalNormalAbove N M → ∃ i, component i = M
  carrier : Subgroup G
  [carrier_normal : carrier.Normal]
  carrier_eq : carrier = ⨆ i, component i
  generator : G
  generated :
    Subgroup.normalClosure (Set.range (fun _ : Fin 1 ↦ generator)) ⊔ N =
      carrier

attribute [instance]
  FiniteRelativeSocleGeneratorData.base_normal
  FiniteRelativeSocleGeneratorData.component_fintype
  FiniteRelativeSocleGeneratorData.carrier_normal

namespace FiniteRelativeSocleGeneratorData

variable {G : Type} [Group G] [Finite G]
  {N : Subgroup G}
  (D : FiniteRelativeSocleGeneratorData G N)

private theorem component_le_carrier (i : D.Component) :
    D.component i ≤ D.carrier := by
  rw [D.carrier_eq]
  exact le_iSup D.component i

/-- Transport a complete relative-socle certificate through a literal group
equivalence. -/
noncomputable def mapEquiv {H : Type} [Group H] [Finite H]
    (e : G ≃* H) :
    FiniteRelativeSocleGeneratorData H (e.mapSubgroup N) := by
  letI : N.Normal := D.base_normal
  letI : (e.mapSubgroup N).Normal :=
    D.base_normal.map e.toMonoidHom e.surjective
  let E : Subgroup G ≃o Subgroup H := e.mapSubgroup
  have himage : e.toMonoidHom ''
      Set.range (fun _ : Fin 1 ↦ D.generator) =
      Set.range (fun _ : Fin 1 ↦ e D.generator) := by
    ext x
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨D.generator, ⟨i, rfl⟩, rfl⟩
  exact
    { Component := D.Component
      component := fun i ↦ E (D.component i)
      component_minimal := fun i ↦
        (D.component_minimal i).map_equiv e
      component_complete := by
        intro K hK
        have hback := hK.map_equiv e.symm
        change IsMinimalNormalAbove (E.symm (E N)) (E.symm K) at hback
        have hback' : IsMinimalNormalAbove N (E.symm K) := by
          simpa only [E.symm_apply_apply] using hback
        obtain ⟨i, hi⟩ := D.component_complete
          (E.symm K) hback'
        exact ⟨i, calc
          E (D.component i) = E (E.symm K) := congrArg E hi
          _ = K := E.apply_symm_apply K⟩
      carrier := E D.carrier
      base_normal := D.base_normal.map e.toMonoidHom e.surjective
      carrier_normal := D.carrier_normal.map e.toMonoidHom e.surjective
      carrier_eq := by
        rw [D.carrier_eq, Subgroup.map_iSup]
      generator := e D.generator
      generated := by
        calc
          Subgroup.normalClosure
                (Set.range (fun _ : Fin 1 ↦ e D.generator)) ⊔
              E N =
              (Subgroup.normalClosure
                (Set.range (fun _ : Fin 1 ↦ D.generator))).map
                  e.toMonoidHom ⊔ E N := by
            rw [Subgroup.map_normalClosure _ _ e.surjective, himage]
          _ = (Subgroup.normalClosure
                (Set.range (fun _ : Fin 1 ↦ D.generator)) ⊔ N).map
                  e.toMonoidHom := by rw [Subgroup.map_sup]
          _ = E D.carrier := by rw [D.generated] }

/-- The image of the checked relative-atom supremum is exactly the quotient
socle. -/
theorem carrier_map_eq_socle :
    D.carrier.map (QuotientGroup.mk' N) = finiteGroupSocle (G ⨸ N) := by
  letI : N.Normal := D.base_normal
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, D.carrier_eq]
    apply iSup_le
    intro i
    rw [← Subgroup.map_le_iff_le_comap]
    intro x hx
    exact Subgroup.subset_normalClosure
      ⟨(D.component i).map (QuotientGroup.mk' N),
        (D.component_minimal i).map_quotient, hx⟩
  · rw [finiteGroupSocle]
    apply Subgroup.normalClosure_le_normal
    rintro x ⟨L, hL, hx⟩
    obtain ⟨i, hi⟩ := D.component_complete
      (L.comap (QuotientGroup.mk' N))
      (IsMinimalNormalAbove.comap_quotient L hL)
    have hLe : L ≤ D.carrier.map (QuotientGroup.mk' N) := by
      calc
        L = (L.comap (QuotientGroup.mk' N)).map
              (QuotientGroup.mk' N) :=
          (Subgroup.map_comap_eq_self_of_surjective
            (QuotientGroup.mk'_surjective N) L).symm
        _ = (D.component i).map (QuotientGroup.mk' N) := by rw [hi]
        _ ≤ D.carrier.map (QuotientGroup.mk' N) :=
          Subgroup.map_mono (D.component_le_carrier i)
    exact hLe hx

/-- The checked original element gives a one-position normal generator of
the quotient socle. -/
noncomputable def quotientSocleGenerator :
    SocleNormalGeneratorBound (G ⨸ N) 1 := by
  letI : N.Normal := D.base_normal
  let x : Fin 1 → G := fun _ ↦ D.generator
  let xq : Fin 1 → G ⨸ N := fun i ↦ QuotientGroup.mk' N (x i)
  refine ⟨xq, ?_⟩
  have himage : (QuotientGroup.mk' N) '' Set.range x = Set.range xq := by
    ext q
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, ⟨i, rfl⟩, rfl⟩
  calc
    Subgroup.normalClosure (Set.range xq) =
        (Subgroup.normalClosure (Set.range x)).map
          (QuotientGroup.mk' N) := by
      rw [Subgroup.map_normalClosure _ _
        (QuotientGroup.mk'_surjective N), himage]
    _ = (Subgroup.normalClosure (Set.range x) ⊔ N).map
          (QuotientGroup.mk' N) := by
      rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
    _ = D.carrier.map (QuotientGroup.mk' N) := by rw [D.generated]
    _ = finiteGroupSocle (G ⨸ N) := D.carrier_map_eq_socle

end FiniteRelativeSocleGeneratorData

namespace Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry

variable {U : Type} [Group U] [Finite U]
  (R : FiniteNormalStateRegistry U)

/-- Transport a complete finite normal registry through a group equivalence
while retaining its original finite state type. -/
noncomputable def mapEquiv {V : Type} [Group V] [Finite V]
    (e : U ≃* V) :
    FiniteNormalStateRegistry V where
  State := R.State
  state i := e.mapSubgroup (R.state i)
  state_normal i := (R.state_normal i).map e.toMonoidHom e.surjective
  state_injective := by
    intro i j hij
    exact R.state_injective (e.mapSubgroup.injective hij)
  complete := by
    intro N hN
    letI : N.Normal := hN
    let M : Subgroup U := N.comap e.toMonoidHom
    letI : M.Normal := hN.comap e.toMonoidHom
    obtain ⟨i, hi⟩ := R.complete M
    refine ⟨i, ?_⟩
    calc
      e.mapSubgroup (R.state i) = e.mapSubgroup M := by rw [hi]
      _ = N := Subgroup.map_comap_eq_self_of_surjective e.surjective N

/-- Finite-state formulation of being minimal strictly above a selected
base state.  It quantifies only over the checked registry. -/
def IsMinimalStateAbove (base j : R.State) : Prop :=
  R.state base < R.state j ∧
    ∀ k : R.State, R.state base < R.state k →
      R.state k ≤ R.state j → R.state k = R.state j

theorem isMinimalNormalAbove_state_iff (base j : R.State) :
    IsMinimalNormalAbove (R.state base) (R.state j) ↔
      R.IsMinimalStateAbove base j := by
  constructor
  · intro h
    exact ⟨h.2.1, fun k hbase hle ↦
      h.2.2 (R.state k) (R.state_normal k) hbase hle⟩
  · rintro ⟨hbase, hminimal⟩
    refine ⟨R.state_normal j, hbase, ?_⟩
    intro K hK hbaseK hKle
    letI : K.Normal := hK
    obtain ⟨k, hk⟩ := R.complete K
    have hbaseState : R.state base < R.state k := by
      simpa only [hk] using hbaseK
    have hstateLe : R.state k ≤ R.state j := by
      simpa only [hk] using hKle
    exact (hminimal k hbaseState hstateLe).trans hk

/-- Construct relative-socle data from finite state indices in a complete
normal registry.  The hypotheses are finite subgroup equalities and order
relations, so generated literal rows can discharge them by kernel-checked
decisions. -/
noncomputable def relativeSocleGeneratorDataOfStates
    (base carrier : R.State)
    (Component : Type) [Fintype Component]
    (componentState : Component → R.State)
    (component_minimal : ∀ i,
      R.IsMinimalStateAbove base (componentState i))
    (component_complete : ∀ j,
      R.IsMinimalStateAbove base j →
        ∃ i, componentState i = j)
    (carrier_eq : R.state carrier =
      ⨆ i, R.state (componentState i))
    (generator : U)
    (generated :
      Subgroup.normalClosure (Set.range (fun _ : Fin 1 ↦ generator)) ⊔
        R.state base = R.state carrier) :
    FiniteRelativeSocleGeneratorData U (R.state base) :=
  { Component := Component
    base_normal := R.state_normal base
    component := fun i ↦ R.state (componentState i)
    component_minimal := fun i ↦
      (R.isMinimalNormalAbove_state_iff base (componentState i)).2
        (component_minimal i)
    component_complete := by
      intro M hM
      letI : M.Normal := hM.1
      obtain ⟨j, hj⟩ := R.complete M
      have hjmin : R.IsMinimalStateAbove base j :=
        (R.isMinimalNormalAbove_state_iff base j).1 (hj ▸ hM)
      obtain ⟨i, hi⟩ := component_complete j hjmin
      exact ⟨i, congrArg R.state hi |>.trans hj⟩
    carrier := R.state carrier
    carrier_normal := R.state_normal carrier
    carrier_eq := carrier_eq
    generator := generator
    generated := generated }

/-- One checked relative-socle certificate on every finite state. -/
structure QuotientSocleGeneratorFamily : Type 1 where
  data : ∀ i : R.State,
    FiniteRelativeSocleGeneratorData U (R.state i)

namespace QuotientSocleGeneratorFamily

variable (D : R.QuotientSocleGeneratorFamily)

/-- Dispatch the finite state certificate to an arbitrary literal normal
axis and produce its one-position quotient-socle witness. -/
noncomputable def dispatch
    (N : {N : Subgroup U // N.Normal}) :
    SocleNormalGeneratorBound (U ⨸ N.1) 1 := by
  let i : R.State := R.normalAxisEquiv.symm N
  have hi : R.normalAxis i = N := R.normalAxisEquiv.apply_symm_apply N
  exact cast
    (congrArg
      (fun M : {M : Subgroup U // M.Normal} ↦
        SocleNormalGeneratorBound (U ⨸ M.1) 1) hi)
    (D.data i).quotientSocleGenerator

end QuotientSocleGeneratorFamily
end Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry

end SymmetricSubgroupAsymptotics

end
