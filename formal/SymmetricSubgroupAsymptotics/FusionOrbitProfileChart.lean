import SymmetricSubgroupAsymptotics.FusionPhysicalCharts
import SymmetricSubgroupAsymptotics.OrbitProfileFromOrbits

/-!
# Physical fusion charts from an exact orbit-image chart

An exact relabelling of one literal orbit image determines a physical
orbit/complement chart for the entire original subgroup.  Both restriction
coordinates come from the same original element, and the complementary
action is retained without enlargement or independence assumptions.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.FusionOrbitProfileChart

variable {X Ω Z : Type*} [Fintype X] [Fintype Ω] [Fintype Z]
    (H : Subgroup (Equiv.Perm X)) (o : OrbitProfileFromOrbits.Orbit H)
    (U : Subgroup (Equiv.Perm Ω))

/-- The selected quotient orbit as an invariant subaction of the original
permutation group. -/
def orbitSubaction : SubMulAction H X where
  carrier := o.orbit
  smul_mem' g _ hx := o.mapsTo_smul_orbit g hx

variable (eO : Ω ≃ o.orbit)
    (eC : Z ≃ ↥((orbitSubaction H o)ᶜ))

/-- The selected orbit and its complete set complement partition `X`. -/
def chart : Ω ⊕ Z ≃ X :=
  (Equiv.sumCongr eO eC).trans
    (Equiv.Set.sumCompl (orbitSubaction H o : Set X))

omit [Fintype X] [Fintype Ω] [Fintype Z] in
@[simp] theorem chart_inl (x : Ω) :
    chart H o eO eC (Sum.inl x) = (eO x : X) := rfl

omit [Fintype X] [Fintype Ω] [Fintype Z] in
@[simp] theorem chart_inr (z : Z) :
    chart H o eO eC (Sum.inr z) = (eC z : X) := rfl

def firstHom : H →* Equiv.Perm Ω :=
  eO.symm.permCongrHom.toMonoidHom.comp (MulAction.toPermHom H o.orbit)

def secondHom : H →* Equiv.Perm Z :=
  eC.symm.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom H ↥((orbitSubaction H o)ᶜ))

def pairHom : H →* Equiv.Perm Ω × Equiv.Perm Z :=
  (firstHom H o eO).prod (secondHom H o eC)

omit [Fintype X] [Fintype Ω] [Fintype Z] in
/-- Both chart coordinates are restrictions of the same original element. -/
theorem chart_pairHom_apply (g : H) (x : Ω ⊕ Z) :
    chart H o eO eC
        (Equiv.Perm.sumCongrHom Ω Z (pairHom H o eO eC g) x) =
      (g : Equiv.Perm X) (chart H o eO eC x) := by
  rcases x with x | z
  · change chart H o eO eC (Sum.inl (firstHom H o eO g x)) =
      (g : Equiv.Perm X) (chart H o eO eC (Sum.inl x))
    rw [chart_inl,chart_inl]
    change ((eO (eO.symm (g • eO x))) : X) = _
    rw [Equiv.apply_symm_apply]
    rfl
  · change chart H o eO eC (Sum.inr (secondHom H o eC g z)) =
      (g : Equiv.Perm X) (chart H o eO eC (Sum.inr z))
    rw [chart_inr,chart_inr]
    change ((eC (eC.symm (g • eC z))) : X) = _
    rw [Equiv.apply_symm_apply]
    rfl

omit [Fintype X] [Fintype Ω] [Fintype Z] in
theorem chart_conjugate_pair (g : H) :
    (chart H o eO eC).symm.permCongr (g : Equiv.Perm X) =
      Equiv.Perm.sumCongrHom Ω Z (pairHom H o eO eC g) := by
  apply Equiv.ext
  intro x
  apply (chart H o eO eC).injective
  change chart H o eO eC ((chart H o eO eC).symm
    ((g : Equiv.Perm X) (chart H o eO eC x))) = _
  rw [Equiv.apply_symm_apply]
  exact (chart_pairHom_apply H o eO eC g x).symm

omit [Fintype X] [Fintype Ω] [Fintype Z] in
/-- Every original element preserves the selected orbit block. -/
theorem chart_preserves :
    ∀ k ∈ relabelSubgroup (chart H o eO eC).symm H,
      Set.MapsTo k (Set.range (Sum.inl : Ω → Ω ⊕ Z))
        (Set.range (Sum.inl : Ω → Ω ⊕ Z)) := by
  intro k hk
  change k ∈ H.map (chart H o eO eC).symm.permCongrHom.toMonoidHom at hk
  obtain ⟨g,hg,rfl⟩ := hk
  rw [show (chart H o eO eC).symm.permCongrHom.toMonoidHom g =
      Equiv.Perm.sumCongrHom Ω Z (pairHom H o eO eC ⟨g,hg⟩)
    from chart_conjugate_pair H o eO eC ⟨g,hg⟩]
  rintro _ ⟨x,rfl⟩
  exact ⟨firstHom H o eO ⟨g,hg⟩ x,rfl⟩

omit [Fintype X] [Fintype Ω] [Fintype Z] in
/-- The unrestricted block pullback is the range of the two simultaneous
restriction maps. -/
theorem blockPullback_eq_range :
    fusionPhysicalBlockPullback (relabelSubgroup (chart H o eO eC).symm H) =
      (pairHom H o eO eC).range := by
  ext p
  constructor
  · intro hp
    change Equiv.Perm.sumCongrHom Ω Z p ∈
      H.map (chart H o eO eC).symm.permCongrHom.toMonoidHom at hp
    obtain ⟨g,hg,he⟩ := hp
    refine ⟨⟨g,hg⟩, ?_⟩
    apply Equiv.Perm.sumCongrHom_injective
    exact (chart_conjugate_pair H o eO eC ⟨g,hg⟩).symm.trans he
  · rintro ⟨g,rfl⟩
    change Equiv.Perm.sumCongrHom Ω Z (pairHom H o eO eC g) ∈
      H.map (chart H o eO eC).symm.permCongrHom.toMonoidHom
    exact ⟨g,g.property,chart_conjugate_pair H o eO eC g⟩

omit [Fintype X] [Fintype Ω] [Fintype Z] in
/-- The first physical projection is exactly the supplied original action
when its relabelled action is the selected orbit image. -/
theorem chart_projection_eq
    (himage : relabelSubgroup eO U = OrbitProfileFromOrbits.orbitImage H o) :
    (fusionPhysicalBlockPullback
      (relabelSubgroup (chart H o eO eC).symm H)).map
        (MonoidHom.fst (Equiv.Perm Ω) (Equiv.Perm Z)) = U := by
  rw [blockPullback_eq_range,MonoidHom.map_range]
  rw [show (MonoidHom.fst (Equiv.Perm Ω) (Equiv.Perm Z)).comp
      (pairHom H o eO eC) = firstHom H o eO from rfl]
  rw [firstHom,MonoidHom.range_comp]
  change relabelSubgroup eO.symm (OrbitProfileFromOrbits.orbitImage H o) = U
  rw [← himage,relabelSubgroup_symm]

omit [Fintype X] in
/-- The exact original subgroup enters the fixed physical fusion family.
The survival predicate is evaluated on its full deleted model. -/
theorem mem_relabelled_family
    (himage : relabelSubgroup eO U = OrbitProfileFromOrbits.orbitImage H o)
    (P : Subgroup (U × Equiv.Perm Z) → Prop)
    (hP : P (fusionDeletedModel U
      (relabelSubgroup (chart H o eO eC).symm H))) :
    H ∈ FusionRelabelledFamily (chart H o eO eC)
      (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) := by
  let K := relabelSubgroup (chart H o eO eC).symm H
  have hm : K ∈ FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P) :=
    fusionDeletedModel_mem_family U K (chart_preserves H o eO eC)
      (chart_projection_eq H o U eO eC himage) P hP
  refine ⟨⟨K,hm⟩, ?_⟩
  exact relabelSubgroup_symm (chart H o eO eC).symm H

end SymmetricSubgroupAsymptotics.FusionOrbitProfileChart

end
