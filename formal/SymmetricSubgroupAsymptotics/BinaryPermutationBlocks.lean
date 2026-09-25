import SymmetricSubgroupAsymptotics.FiniteGroupCertificates
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Exact permutation restrictions from generator intertwiners

An injective coordinate embedding and finite generator equations construct
an actual homomorphism onto the complete restricted action. No action
catalogue name or declared group order is used.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {X Y ι : Type*}

/-- Pairs of permutations that intertwine a fixed coordinate map. -/
def permutationIntertwiner (e : Y → X) : Subgroup (Equiv.Perm X × Equiv.Perm Y) where
  carrier := {p | ∀ y, p.1 (e y) = e (p.2 y)}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro a b ha hb y
    change a.1 (b.1 (e y)) = e (a.2 (b.2 y))
    rw [hb, ha]
  inv_mem' := by
    intro a ha y
    apply a.1.injective
    simpa using (ha (a.2⁻¹ y)).symm

/-- A literal displayed block, certified on the original generators. -/
structure PermutationBlockChart (s : ι → Equiv.Perm X) where
  embedding : Y ↪ X
  images : ι → Equiv.Perm Y
  intertwine : ∀ j y, s j (embedding y) = embedding (images j y)

namespace PermutationBlockChart

variable {s : ι → Equiv.Perm X} (C : PermutationBlockChart (Y := Y) s)

def graph : Subgroup (Equiv.Perm X × Equiv.Perm Y) :=
  Subgroup.closure (Set.range (fun j => (s j, C.images j)))

theorem graph_intertwine : C.graph ≤ permutationIntertwiner C.embedding := by
  apply (Subgroup.closure_le _).mpr
  rintro p ⟨j,rfl⟩
  exact C.intertwine j

theorem first_image : C.graph.map (MonoidHom.fst _ _) =
    Subgroup.closure (Set.range s) := by
  rw [graph, MonoidHom.map_closure]
  congr 1
  ext x
  simp

theorem second_image : C.graph.map (MonoidHom.snd _ _) =
    Subgroup.closure (Set.range C.images) := by
  rw [graph, MonoidHom.map_closure]
  congr 1
  ext x
  simp

def first : C.graph →* Subgroup.closure (Set.range s) :=
  ((MonoidHom.fst _ _).comp C.graph.subtype).codRestrict _ (fun x => by
    rw [← C.first_image]
    exact ⟨x,x.property,rfl⟩)

theorem first_surjective : Function.Surjective C.first := by
  rintro ⟨x,hx⟩
  rw [← C.first_image] at hx
  obtain ⟨y,hy,he⟩ := hx
  exact ⟨⟨y,hy⟩,Subtype.ext he⟩

theorem first_injective : Function.Injective C.first := by
  apply (MonoidHom.ker_eq_bot_iff C.first).mp
  apply le_antisymm _ bot_le
  intro x hx
  have hx1 : (x : Equiv.Perm X × Equiv.Perm Y).1 = 1 := congrArg Subtype.val hx
  have hx2 : (x : Equiv.Perm X × Equiv.Perm Y).2 = 1 := by
    ext y
    apply C.embedding.injective
    have h := C.graph_intertwine x.property y
    simpa only [hx1, Equiv.Perm.one_apply] using h.symm
  exact Subtype.ext (Prod.ext hx1 hx2)

def firstEquiv : C.graph ≃* Subgroup.closure (Set.range s) :=
  MulEquiv.ofBijective C.first ⟨C.first_injective,C.first_surjective⟩

/-- Actual restriction to the displayed block coordinates. -/
def hom : Subgroup.closure (Set.range s) →* Equiv.Perm Y :=
  ((MonoidHom.snd _ _).comp C.graph.subtype).comp C.firstEquiv.symm.toMonoidHom

theorem hom_graph (x : Subgroup.closure (Set.range s)) :
    ((x : Equiv.Perm X), C.hom x) ∈ C.graph := by
  have hx := (C.firstEquiv.symm x).property
  have hfirst : (C.firstEquiv.symm x : Equiv.Perm X × Equiv.Perm Y).1 = x :=
    congrArg Subtype.val (C.firstEquiv.apply_symm_apply x)
  simpa only [← hfirst] using hx

/-- The homomorphism agrees with the original physical permutation. -/
theorem hom_intertwine (x : Subgroup.closure (Set.range s)) (y : Y) :
    (x : Equiv.Perm X) (C.embedding y) = C.embedding (C.hom x y) :=
  C.graph_intertwine (C.hom_graph x) y

theorem hom_generator (j : ι) :
    C.hom ⟨s j,Subgroup.subset_closure (Set.mem_range_self j)⟩ = C.images j := by
  ext y
  apply C.embedding.injective
  exact (C.hom_intertwine _ y).symm.trans (C.intertwine j y)

/-- The block projection is onto the entire literal generated action. -/
theorem hom_range : C.hom.range = Subgroup.closure (Set.range C.images) := by
  apply le_antisymm
  · rintro y ⟨x,rfl⟩
    rw [← C.second_image]
    exact ⟨((x : Equiv.Perm X),C.hom x),C.hom_graph x,rfl⟩
  · apply (Subgroup.closure_le _).mpr
    rintro y ⟨j,rfl⟩
    exact ⟨⟨s j,Subgroup.subset_closure (Set.mem_range_self j)⟩,C.hom_generator j⟩

end PermutationBlockChart

/-- The joint block action retains every original physical point. -/
theorem permutationBlock_joint_injective {κ : Type*} {Y : κ → Type*}
    {s : ι → Equiv.Perm X} (C : ∀ i, PermutationBlockChart (Y := Y i) s)
    (hcover : ∀ x : X, ∃ i y, (C i).embedding y = x) :
    Function.Injective (fun g : Subgroup.closure (Set.range s) =>
      fun i => (C i).hom g) := by
  intro g h he
  apply Subtype.ext
  ext x
  obtain ⟨i,y,rfl⟩ := hcover x
  rw [(C i).hom_intertwine, (C i).hom_intertwine]
  exact congrArg (fun f : Equiv.Perm (Y i) => (C i).embedding (f y))
    (congrFun he i)

/-- Two finite generating families generate the same literal group when
checked words express every generator in each direction. -/
theorem subgroup_closure_eq_of_generator_words {G ι κ : Type*} [Group G]
    (s : ι → G) (t : κ → G) (forward : ι → List κ) (backward : κ → List ι)
    (hf : ∀ i, s i = ((forward i).map t).prod)
    (hb : ∀ j, t j = ((backward j).map s).prod) :
    Subgroup.closure (Set.range s) = Subgroup.closure (Set.range t) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨i,rfl⟩
    rw [hf]
    apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hy
    exact Subgroup.subset_closure (Set.mem_range_self j)
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨j,rfl⟩
    rw [hb]
    apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hy
    exact Subgroup.subset_closure (Set.mem_range_self i)

theorem subgroup_closure_single_generator_isCyclic {G : Type*} [Group G]
    (s : Fin 1 → G) : IsCyclic (Subgroup.closure (Set.range s)) := by
  have hr : Set.range s = {s 0} := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩
      congr
      exact Subsingleton.elim _ _
    · intro hx
      exact ⟨0,hx.symm⟩
  rw [hr, ← Subgroup.zpowers_eq_closure]
  infer_instance

end SymmetricSubgroupAsymptotics
