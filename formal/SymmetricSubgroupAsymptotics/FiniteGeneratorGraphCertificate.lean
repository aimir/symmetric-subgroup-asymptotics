import SymmetricSubgroupAsymptotics.DerivedGeneratorWords

/-! Selected finite graph certificates for actual generator-image maps.
Only right-generator transitions, inverse rows and positive words are
checked. They prove an actual homomorphism on the original generated
subgroup; generator images alone are never treated as a homomorphism. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

structure FiniteGeneratorGraphCertificate {G H I J : Type}
    [Group G] [Group H] (source : J → G) (target : J → H) where
  state : I → G × H
  word : I → List J
  word_eq : ∀ i, ((word i).map (fun j => (source j, target j))).prod = state i
  identity : I
  identity_eq : state identity = 1
  step : I → J → I
  step_eq : ∀ i j, state (step i j) = state i * (source j, target j)
  inverse : I → I
  inverse_eq : ∀ i, state (inverse i) = (state i)⁻¹
  source_injective : Function.Injective (fun i => (state i).1)

namespace FiniteGeneratorGraphCertificate
variable {G H I J : Type} [Group G] [Group H]
  {source : J → G} {target : J → H}
  (C : FiniteGeneratorGraphCertificate (I := I) source target)

def graph (_certificate : FiniteGeneratorGraphCertificate (I := I) source target) :
    Subgroup (G × H) :=
  Subgroup.closure (Set.range (fun j => (source j, target j)))

private theorem right_word (i : I) (w : List J) :
    ∃ k, state C i * (w.map (fun j => (source j, target j))).prod = state C k := by
  induction w generalizing i with
  | nil => exact ⟨i, by simp⟩
  | cons j w ih =>
      obtain ⟨k, hk⟩ := ih (C.step i j)
      refine ⟨k, ?_⟩
      simpa only [List.map_cons, List.prod_cons, C.step_eq, mul_assoc] using hk

private def rangeSubgroup : Subgroup (G × H) where
  carrier := Set.range C.state
  one_mem' := ⟨C.identity, C.identity_eq⟩
  mul_mem' := by
    rintro x y ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := C.right_word i (C.word j)
    exact ⟨k, (by rw [C.word_eq] at hk; exact hk.symm)⟩
  inv_mem' := by
    rintro x ⟨i, rfl⟩
    exact ⟨C.inverse i, C.inverse_eq i⟩

theorem range_eq_graph : C.rangeSubgroup = C.graph := by
  apply le_antisymm
  · rintro x ⟨i, rfl⟩
    rw [← C.word_eq i]
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact Subgroup.subset_closure (Set.mem_range_self j)
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨j, rfl⟩
    refine ⟨C.step C.identity j, ?_⟩
    rw [C.step_eq, C.identity_eq, one_mul]

def Source (_certificate : FiniteGeneratorGraphCertificate (I := I) source target) :=
  Subgroup.closure (Set.range source)
def Target (_certificate : FiniteGeneratorGraphCertificate (I := I) source target) :=
  Subgroup.closure (Set.range target)

private theorem fst_image : C.graph.map (MonoidHom.fst G H) = C.Source := by
  rw [graph, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, MonoidHom.fst]
  rfl
private theorem snd_image : C.graph.map (MonoidHom.snd G H) = C.Target := by
  rw [graph, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, MonoidHom.snd]
  rfl

def first : C.graph →* C.Source :=
  ((MonoidHom.fst G H).comp C.graph.subtype).codRestrict C.Source (by
    intro x
    rw [← C.fst_image]
    exact ⟨x, x.2, rfl⟩)
def second : C.graph →* C.Target :=
  ((MonoidHom.snd G H).comp C.graph.subtype).codRestrict C.Target (by
    intro x
    rw [← C.snd_image]
    exact ⟨x, x.2, rfl⟩)

theorem first_bijective : Function.Bijective C.first := by
  constructor
  · intro x y hxy
    have hx : (x : G × H) ∈ C.rangeSubgroup := C.range_eq_graph.symm ▸ x.2
    have hy : (y : G × H) ∈ C.rangeSubgroup := C.range_eq_graph.symm ▸ y.2
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hy
    have he : (C.state i).1 = (C.state j).1 := by
      rw [hi, hj]
      exact congrArg Subtype.val hxy
    have hij := C.source_injective he
    apply Subtype.ext
    exact hi.symm.trans ((congrArg C.state hij).trans hj)
  · intro x
    have hx : (x : G) ∈ C.graph.map (MonoidHom.fst G H) := C.fst_image.symm ▸ x.2
    obtain ⟨g, hg, he⟩ := hx
    refine ⟨⟨g, hg⟩, ?_⟩
    exact Subtype.ext he

theorem second_surjective : Function.Surjective C.second := by
  intro x
  have hx : (x : H) ∈ C.graph.map (MonoidHom.snd G H) := C.snd_image.symm ▸ x.2
  obtain ⟨g, hg, he⟩ := hx
  exact ⟨⟨g, hg⟩, Subtype.ext he⟩

def sourceEquiv : C.graph ≃* C.Source := MulEquiv.ofBijective C.first C.first_bijective

def hom : C.Source →* C.Target := C.second.comp C.sourceEquiv.symm.toMonoidHom

theorem hom_surjective : Function.Surjective C.hom :=
  C.second_surjective.comp C.sourceEquiv.symm.surjective


theorem state_mem (i : I) : C.state i ∈ C.graph :=
  C.range_eq_graph ▸ (show C.state i ∈ C.rangeSubgroup from ⟨i, rfl⟩)

def sourceElement (i : I) : C.Source := C.first ⟨C.state i, C.state_mem i⟩

theorem sourceElement_surjective : Function.Surjective C.sourceElement := by
  intro x
  let y := C.sourceEquiv.symm x
  have hy : (y : G × H) ∈ C.rangeSubgroup := C.range_eq_graph.symm ▸ y.2
  obtain ⟨i, hi⟩ := hy
  refine ⟨i, ?_⟩
  have he : (⟨C.state i, C.state_mem i⟩ : C.graph) = y := Subtype.ext hi
  change C.sourceEquiv ⟨C.state i, C.state_mem i⟩ = x
  rw [he, C.sourceEquiv.apply_symm_apply]

theorem hom_sourceElement (i : I) :
    (C.hom (C.sourceElement i) : H) = (C.state i).2 := by
  change ((C.second (C.sourceEquiv.symm
    (C.sourceEquiv ⟨C.state i, C.state_mem i⟩))) : H) = _
  rw [C.sourceEquiv.symm_apply_apply]
  rfl

theorem sourceElement_val (i : I) : (C.sourceElement i : G) = (C.state i).1 := rfl

end FiniteGeneratorGraphCertificate
end SymmetricSubgroupAsymptotics
