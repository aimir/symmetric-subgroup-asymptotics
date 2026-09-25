import SymmetricSubgroupAsymptotics.BinaryNormalGeneratorSteps
import SymmetricSubgroupAsymptotics.FiniteCayleyMaps

/-!
# Shared literal top-normal registries

Every state is the kernel of a checked permutation quotient cover.  The
finite masks describe those actual kernels.  Closure under all central
involution lifts proves completeness; neither a normal-subgroup catalogue
nor a declared quotient order is a hypothesis.
-/

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G ι I : Type*} [Group G] [Fintype G]

/-- A finite mask for the exact kernel of one faithful quotient cover. -/
structure BinaryTopKernelData (G : Type*) [Group G] where
  degree : ℕ
  hom : G →* Equiv.Perm (Fin degree)
  mask : G → Bool
  mask_eq : ∀ x, mask x = true ↔ hom x = 1

namespace BinaryTopKernelData

variable (S : BinaryTopKernelData G)

abbrev kernel : Subgroup G := S.hom.ker

/-- Transport the same cover through an exact identification of its
original group; its literal kernel is transported by that same map. -/
def transport {H : Type*} [Group H] (e : G ≃* H) : BinaryTopKernelData H where
  degree := S.degree
  hom := S.hom.comp e.symm.toMonoidHom
  mask x := S.mask (e.symm x)
  mask_eq x := S.mask_eq (e.symm x)

omit [Fintype G] in
theorem transport_kernel {H : Type*} [Group H] (e : G ≃* H) :
    (S.transport e).kernel=S.kernel.map e.toMonoidHom := by
  change S.kernel.comap e.symm.toMonoidHom=S.kernel.map e.toMonoidHom
  exact Subgroup.comap_equiv_eq_map_symm e.symm S.kernel

def size : ℕ := (Finset.univ.filter (fun x => S.mask x = true)).card

theorem size_eq : S.size = Nat.card S.kernel := by
  classical
  let e : {x : G // S.mask x = true} ≃ S.kernel :=
    Equiv.subtypeEquivRight (fun x => S.mask_eq x)
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

/-- Only original generator commutators need be checked in the finite
rejection test.  Completeness below uses necessity, so no unproved
converse about centrality is required. -/
def liftTests (generators : ι → G) (x : G) : Prop :=
  S.mask x = false ∧ S.mask (x*x) = true ∧
    ∀ j, S.mask (x*generators j/(generators j*x)) = true

omit [Fintype G] in
theorem liftTests_of_central (generators : ι → G) (x : G)
    (hc : QuotientGroup.mk' S.kernel x ∈ Subgroup.center (G ⧸ S.kernel))
    (ho : orderOf (QuotientGroup.mk' S.kernel x) = 2) :
    S.liftTests generators x := by
  obtain ⟨hsq,hne⟩ := (orderOf_eq_prime_iff (p := 2)).mp ho
  have hnot : x ∉ S.kernel := by
    intro hx
    exact hne ((QuotientGroup.eq_one_iff x).mpr hx)
  refine ⟨?_,?_,?_⟩
  · cases hm : S.mask x
    · rfl
    · exact False.elim (hnot ((S.mask_eq x).mp hm))
  · apply (S.mask_eq _).mpr
    have hx : x*x ∈ S.kernel := (QuotientGroup.eq_one_iff _).mp (by
      simpa only [map_mul, pow_two] using hsq)
    exact hx
  · intro j
    apply (S.mask_eq _).mpr
    change x*generators j/(generators j*x) ∈ S.kernel
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' S.kernel (x*generators j/(generators j*x))=1
    rw [map_div, map_mul, map_mul, div_eq_one]
    exact (Subgroup.mem_center_iff.mp hc _).symm

end BinaryTopKernelData

/-- Small checked masks encode the local transitions.  The permutation
covers themselves are actual homomorphisms on the original top group. -/
structure BinaryTopNormalRegistry (generators : ι → G)
    (states : I → BinaryTopKernelData G) where
  bottom : I
  bottom_mask : ∀ x, (states bottom).mask x = true ↔ x = 1
  child : I → G → I
  parent_mem : ∀ i x, (states i).liftTests generators x →
    ∀ y, (states i).mask y = true → (states (child i x)).mask y = true
  lift_mem : ∀ i x, (states i).liftTests generators x →
    (states (child i x)).mask x = true
  child_size : ∀ i x, (states i).liftTests generators x →
    (states (child i x)).size = (states i).size * 2

namespace BinaryTopNormalRegistry

variable {generators : ι → G} {states : I → BinaryTopKernelData G}
    (C : BinaryTopNormalRegistry generators states)

include C

/-- Every normal subgroup of the literal finite binary top occurs as one
of the checked cover kernels. -/
theorem complete (hG : IsPGroup 2 G) (N : Subgroup G) [N.Normal] :
    ∃ i, (states i).kernel = N := by
  apply pGroup_normal_registry_complete hG
    (Set.range (fun i => (states i).kernel)) ?_ ?_ ?_ N
  · refine ⟨C.bottom,?_⟩
    ext x
    exact ((states C.bottom).mask_eq x).symm.trans (C.bottom_mask x)
  · rintro _ ⟨i,rfl⟩
    infer_instance
  · rintro _ ⟨i,rfl⟩ _ z hzc hzo
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (states i).kernel z
    have ht := (states i).liftTests_of_central generators x hzc hzo
    refine ⟨C.child i x,?_⟩
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · rw [normal_step_generated]
      apply sup_le
      · intro y hy
        exact ((states (C.child i x)).mask_eq y).mp
          (C.parent_mem i x ht y (((states i).mask_eq y).mpr hy))
      · apply Subgroup.zpowers_le.mpr
        exact ((states (C.child i x)).mask_eq x).mp (C.lift_mem i x ht)
    · rw [normal_step_card,hzo,← (states i).size_eq,
        ← (states (C.child i x)).size_eq,C.child_size i x ht]

theorem complete_map_of_equiv {H : Type*} [Group H]
    (hG : IsPGroup 2 G) (e : G ≃* H) (N : Subgroup H) [N.Normal] :
    ∃ i, (states i).kernel.map e.toMonoidHom = N := by
  obtain ⟨i,hi⟩ := C.complete hG (N.comap e.toMonoidHom)
  refine ⟨i,?_⟩
  rw [hi,Subgroup.map_comap_eq_self_of_surjective e.surjective]

end BinaryTopNormalRegistry

/-- One complete registry on its literal permutation top.  This packages
different physical top widths without forgetting their actions or covers. -/
structure BinaryCompleteTopRegistry where
  width : ℕ
  top : Subgroup (Equiv.Perm (Fin width))
  count : ℕ
  states : Fin count → BinaryTopKernelData top
  complete : ∀ (N : Subgroup top), N.Normal → ∃ i, (states i).kernel=N

end SymmetricSubgroupAsymptotics
