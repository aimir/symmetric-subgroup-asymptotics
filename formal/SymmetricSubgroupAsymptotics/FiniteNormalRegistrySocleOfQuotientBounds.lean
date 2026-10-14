import SymmetricSubgroupAsymptotics.FiniteNormalRegistryQuotientSocle

/-!
# Registry socle certificates from structural quotient bounds

A structural proof of the socle generator bound for every quotient can feed
the existing finite normal-registry interface. The relative components are
the actual minimal normal subgroups above the selected kernel. Choose lifts
of the quotient's generating tuple; their normal closure modulo the kernel
is exactly the relative socle carrier.

This construction uses finiteness and choice, not an enumeration or a new
certificate hypothesis. It preserves the registry's original state type.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- The supremum of a normal kernel and all its relative minimal normal
subgroups. The kernel is retained even when there are no relative atoms. -/
def relativeNormalSocleCarrier {G : Type} [Group G] (N : Subgroup G) :
    Subgroup G :=
  N ⊔ ⨆ M : {M : Subgroup G // IsMinimalNormalAbove N M}, M.1

/-- A supremum of the relative normal components remains normal. -/
theorem relativeNormalSocleCarrier_normal
    {G : Type} [Group G] (N : Subgroup G) [N.Normal] :
    (relativeNormalSocleCarrier N).Normal := by
  let C := relativeNormalSocleCarrier N
  have hcore : C ≤ C.normalCore := by
    change N ⊔
        (⨆ M : {M : Subgroup G // IsMinimalNormalAbove N M}, M.1) ≤
      C.normalCore
    apply sup_le
    · apply Subgroup.normal_le_normalCore.mpr
      exact le_sup_left
    · apply iSup_le
      intro M
      letI : M.1.Normal := M.2.1
      apply Subgroup.normal_le_normalCore.mpr
      exact le_sup_of_le_right
        (le_iSup
          (fun K : {K : Subgroup G // IsMinimalNormalAbove N K} ↦ K.1) M)
  have hC : C = C.normalCore :=
    le_antisymm hcore C.normalCore_le
  change C.Normal
  rw [hC]
  infer_instance

/-- Relative minimal normal subgroups exhaust the minimal normal subgroups
of the quotient, so their carrier maps onto its socle. -/
theorem relativeNormalSocleCarrier_map_eq_socle
    {G : Type} [Group G] (N : Subgroup G) [N.Normal] :
    (relativeNormalSocleCarrier N).map (QuotientGroup.mk' N) =
      finiteGroupSocle (G ⧸ N) := by
  letI : (relativeNormalSocleCarrier N).Normal :=
    relativeNormalSocleCarrier_normal N
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, relativeNormalSocleCarrier]
    apply sup_le
    · exact QuotientGroup.le_comap_mk' N (finiteGroupSocle (G ⧸ N))
    · apply iSup_le
      intro M
      rw [← Subgroup.map_le_iff_le_comap]
      intro x hx
      exact Subgroup.subset_normalClosure
        ⟨M.1.map (QuotientGroup.mk' N), M.2.map_quotient, hx⟩
  · rw [finiteGroupSocle]
    apply Subgroup.normalClosure_le_normal
    rintro x ⟨L, hL, hx⟩
    have hcomponent :
        L.comap (QuotientGroup.mk' N) ≤ relativeNormalSocleCarrier N := by
      exact le_sup_of_le_right
        (le_iSup
          (fun M : {M : Subgroup G // IsMinimalNormalAbove N M} ↦ M.1)
          ⟨L.comap (QuotientGroup.mk' N),
            IsMinimalNormalAbove.comap_quotient L hL⟩)
    have hLe : L ≤
        (relativeNormalSocleCarrier N).map (QuotientGroup.mk' N) := by
      calc
        L = (L.comap (QuotientGroup.mk' N)).map
              (QuotientGroup.mk' N) :=
          (Subgroup.map_comap_eq_self_of_surjective
            (QuotientGroup.mk'_surjective N) L).symm
        _ ≤ (relativeNormalSocleCarrier N).map (QuotientGroup.mk' N) :=
          Subgroup.map_mono hcomponent
    exact hLe hx

/-- The relative carrier is the exact preimage of the quotient socle. -/
theorem relativeNormalSocleCarrier_eq_comap_socle
    {G : Type} [Group G] (N : Subgroup G) [N.Normal] :
    relativeNormalSocleCarrier N =
      (finiteGroupSocle (G ⧸ N)).comap (QuotientGroup.mk' N) := by
  have hN : N ≤ relativeNormalSocleCarrier N := le_sup_left
  have h := congrArg (Subgroup.comap (QuotientGroup.mk' N))
    (relativeNormalSocleCarrier_map_eq_socle N)
  simpa only [QuotientGroup.comap_map_mk', sup_eq_right.mpr hN] using h

namespace FiniteRelativeSocleGeneratorData

/-- Recover the existing finite relative-socle certificate from a structural
quotient-socle bound. The component type consists of actual relative atoms;
chosen lifts of the quotient generators generate their carrier modulo `N`. -/
noncomputable def ofQuotientSocleGeneratorBound
    {G : Type} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] {t : ℕ}
    (h : SocleNormalGeneratorBound (G ⧸ N) t) :
    FiniteRelativeSocleGeneratorData G N t := by
  let Component := {M : Subgroup G // IsMinimalNormalAbove N M}
  letI : Finite Component := Finite.of_injective
    (fun M : Component ↦ (M.1 : Set G)) (by
      intro A B hAB
      exact Subtype.ext (SetLike.coe_injective hAB))
  letI : Fintype Component := Fintype.ofFinite Component
  let xq : Fin t → G ⧸ N := Classical.choose h
  have hxq : Subgroup.normalClosure (Set.range xq) =
      finiteGroupSocle (G ⧸ N) := Classical.choose_spec h
  let x : Fin t → G := fun i ↦
    Classical.choose ((QuotientGroup.mk'_surjective N) (xq i))
  have hx (i : Fin t) : QuotientGroup.mk' N (x i) = xq i :=
    Classical.choose_spec ((QuotientGroup.mk'_surjective N) (xq i))
  have himage : (QuotientGroup.mk' N) '' Set.range x = Set.range xq := by
    ext y
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hx i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, ⟨i, rfl⟩, hx i⟩
  have hmap : (Subgroup.normalClosure (Set.range x)).map
      (QuotientGroup.mk' N) = finiteGroupSocle (G ⧸ N) := by
    rw [Subgroup.map_normalClosure _ _
      (QuotientGroup.mk'_surjective N), himage]
    exact hxq
  have hgenerated : Subgroup.normalClosure (Set.range x) ⊔ N =
      relativeNormalSocleCarrier N := by
    have hcomap := congrArg (Subgroup.comap (QuotientGroup.mk' N)) hmap
    calc
      Subgroup.normalClosure (Set.range x) ⊔ N =
          N ⊔ Subgroup.normalClosure (Set.range x) := sup_comm _ _
      _ = (finiteGroupSocle (G ⧸ N)).comap (QuotientGroup.mk' N) := by
        simpa only [QuotientGroup.comap_map_mk'] using hcomap
      _ = relativeNormalSocleCarrier N :=
        (relativeNormalSocleCarrier_eq_comap_socle N).symm
  exact
    { base_normal := inferInstance
      Component := Component
      component := fun M ↦ M.1
      component_minimal := fun M ↦ M.2
      component_complete := fun M hM ↦ ⟨⟨M, hM⟩, rfl⟩
      carrier := relativeNormalSocleCarrier N
      carrier_normal := relativeNormalSocleCarrier_normal N
      carrier_eq := rfl
      generator := x
      generated := hgenerated }

end FiniteRelativeSocleGeneratorData

namespace Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry
namespace QuotientSocleGeneratorFamily

/-- Structural bounds on all normal quotients supply the existing finite
registry family, keeping every original state and its exact subgroup. -/
noncomputable def ofQuotientBounds
    {G : Type} [Group G] [Finite G]
    (R : FiniteNormalStateRegistry G) {t : ℕ}
    (h : ∀ N : {N : Subgroup G // N.Normal},
      SocleNormalGeneratorBound (G ⧸ N.1) t) :
    R.QuotientSocleGeneratorFamily t where
  data i := by
    letI : (R.state i).Normal := R.state_normal i
    exact FiniteRelativeSocleGeneratorData.ofQuotientSocleGeneratorBound
      (R.state i) (h ⟨R.state i, R.state_normal i⟩)

end QuotientSocleGeneratorFamily
end Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry
end SymmetricSubgroupAsymptotics

end
