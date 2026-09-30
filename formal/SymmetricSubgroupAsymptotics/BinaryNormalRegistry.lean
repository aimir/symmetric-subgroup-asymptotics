import SymmetricSubgroupAsymptotics.BinaryNormalCosets
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Complete normal registries from exact quotient rows

A checked row is an element of the original quotient. Every central
involution is tested on these rows, and a child is identified by original
normal generators, one original lift, and its doubled order. Consequently
local edge checks imply completeness for every normal subgroup of the
original finite 2-group. Acceptance is subsequently checked at each listed
literal normal subgroup; numerical signatures do not replace that check.
-/

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G ι : Type*} [Group G] [Finite G]

/-- Data for one literal normal state, with its original quotient chart. -/
structure BinaryNormalState (generators : ι → G) where
  kernel : Subgroup G
  normal : kernel.Normal
  generatorCount : ℕ
  normalGenerators : Fin generatorCount → G
  generated : Subgroup.closure (Set.range normalGenerators)=kernel
  quotientCount : ℕ
  cardinal : Nat.card kernel*quotientCount=Nat.card G
  cosets : letI := normal
    BinaryNormalCosetCertificate generators kernel quotientCount
  prev : Fin quotientCount → ι → Fin quotientCount
  prev_next : ∀ i j, cosets.next (prev i j) j=i

attribute [instance] BinaryNormalState.normal

namespace BinaryNormalState

variable {generators : ι → G} (S : BinaryNormalState generators)
    (hgen : Subgroup.closure (Set.range generators)=⊤)

/-- The checked quotient-row count is the actual index of the retained
normal subgroup.  This numerical bridge avoids reopening the quotient
enumeration when a later finite classifier supplies an index condition. -/
theorem index_eq_quotientCount : S.kernel.index=S.quotientCount := by
  have hindex := S.kernel.card_mul_index
  have hpositive : 0<Nat.card S.kernel := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hpositive
  exact hindex.trans S.cardinal.symm

abbrev Row := FiniteGroupRow S.quotientCount

@[reducible] def group : Group S.Row :=
  S.cosets.rowGroup hgen S.cardinal S.prev S.prev_next

def quotientEquiv : letI := S.group hgen
    S.Row ≃* G ⧸ S.kernel :=
  S.cosets.rowQuotientEquiv hgen S.cardinal S.prev S.prev_next

def originalMap : letI := S.group hgen
    G →* S.Row :=
  S.cosets.originalMap hgen S.cardinal S.prev S.prev_next

theorem originalMap_surjective : Function.Surjective (S.originalMap hgen) :=
  S.cosets.originalMap_surjective hgen S.cardinal S.prev S.prev_next

theorem originalMap_kernel : letI := S.group hgen
    (S.originalMap hgen).ker=S.kernel :=
  S.cosets.originalMap_kernel hgen S.cardinal S.prev S.prev_next

/-- Centrality and involution order refer to the executable row group,
which is proved equivalent to the full original quotient. -/
def CentralInvolution (z : S.Row) : Prop :=
  letI := S.group hgen
  z ∈ Subgroup.center S.Row ∧ orderOf z=2

/-- The checked row tests cover every actual central quotient involution. -/
theorem centralInvolution_iff (z : S.Row) :
    S.CentralInvolution hgen z ↔
    S.quotientEquiv hgen z ∈ Subgroup.center (G ⧸ S.kernel) ∧
      orderOf (S.quotientEquiv hgen z)=2 := by
  letI := S.group hgen
  unfold CentralInvolution
  constructor
  · rintro ⟨hc,ho⟩
    constructor
    · rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨y,rfl⟩ := (S.quotientEquiv hgen).surjective x
      simpa only [← map_mul] using congrArg (S.quotientEquiv hgen)
        (Subgroup.mem_center_iff.mp hc y)
    · simpa only [MulEquiv.orderOf_eq] using ho
  · rintro ⟨hc,ho⟩
    constructor
    · rw [Subgroup.mem_center_iff]
      intro x
      apply (S.quotientEquiv hgen).injective
      simpa only [map_mul] using Subgroup.mem_center_iff.mp hc (S.quotientEquiv hgen x)
    · simpa only [MulEquiv.orderOf_eq] using ho

/-- A central row's child is established using short original generator
checks and one cardinal equality. The selected lift need not have order 2. -/
theorem child_eq (z : S.Row) (hz : S.CentralInvolution hgen z)
    (T : BinaryNormalState generators)
    (hmem : ∀ j, S.normalGenerators j ∈ T.kernel)
    (hlift : S.cosets.representatives z.index ∈ T.kernel)
    (hcard : Nat.card T.kernel=Nat.card S.kernel*2) :
    (Subgroup.zpowers (S.quotientEquiv hgen z)).comap
      (QuotientGroup.mk' S.kernel)=T.kernel := by
  have ho := ((S.centralInvolution_iff hgen z).mp hz).2
  have he : S.quotientEquiv hgen z=
      QuotientGroup.mk' S.kernel (S.cosets.representatives z.index) :=
    S.cosets.rowQuotientEquiv_apply hgen S.cardinal S.prev S.prev_next z
  rw [he] at ho ⊢
  exact normal_step_eq_of_generators_card S.kernel S.normalGenerators S.generated
    (S.cosets.representatives z.index) T.kernel hmem hlift (by rw [ho]; exact hcard)

/-- Necessary finite tests for a central involution. Only original
source-generator rows are tested for commutation, avoiding a quadratic
quotient multiplication table. -/
def centralRowTests (z : S.Row) : Prop :=
  letI := S.group hgen
  z≠1 ∧ z*z=1 ∧ ∀ j, z*⟨S.cosets.next S.cosets.identity j⟩=
    (⟨S.cosets.next S.cosets.identity j⟩ : S.Row)*z

theorem centralInvolution_rowTests (z : S.Row) (hz : S.CentralInvolution hgen z) :
    S.centralRowTests hgen z := by
  letI := S.group hgen
  obtain ⟨hc,ho⟩ := hz
  obtain ⟨hpow,hne⟩ := (orderOf_eq_prime_iff (p := 2)).mp ho
  refine ⟨hne,by simpa only [pow_two] using hpow,?_⟩
  intro j
  exact (Subgroup.mem_center_iff.mp hc _).symm

end BinaryNormalState

/-- A complete quotient-row certificate for a family of literal normal
states. The children are supplied finite rows; completeness is proved below. -/
structure BinaryNormalRegistry {I : Type*} (generators : ι → G)
    (hgen : Subgroup.closure (Set.range generators)=⊤)
    (states : I → BinaryNormalState generators) where
  bottom : I
  bottom_kernel : (states bottom).kernel=⊥
  child : ∀ i, (states i).Row → I
  generator_mem : ∀ i z, (states i).CentralInvolution hgen z →
    ∀ j, (states i).normalGenerators j ∈ (states (child i z)).kernel
  lift_mem : ∀ i z, (states i).CentralInvolution hgen z →
    (states i).cosets.representatives z.index ∈ (states (child i z)).kernel
  child_card : ∀ i z, (states i).CentralInvolution hgen z →
    Nat.card (states (child i z)).kernel=Nat.card (states i).kernel*2

namespace BinaryNormalRegistry

variable {I : Type*} {generators : ι → G}
    {hgen : Subgroup.closure (Set.range generators)=⊤}
    {states : I → BinaryNormalState generators}
    (C : BinaryNormalRegistry generators hgen states)

include C

/-- Local checked central-involution edges cover every original normal
subgroup. There is no separate enumeration-completeness assumption. -/
theorem complete (hG : IsPGroup 2 G) (N : Subgroup G) [N.Normal] :
    ∃ i, (states i).kernel=N := by
  have h := pGroup_normal_registry_complete hG
    (Set.range (fun i => (states i).kernel))
    ⟨C.bottom,C.bottom_kernel⟩
    (by rintro _ ⟨i,rfl⟩; infer_instance) ?_ N
  · exact h
  · rintro _ ⟨i,rfl⟩ _ z hzc hzo
    let S := states i
    letI := S.group hgen
    obtain ⟨r,hr⟩ := (S.quotientEquiv hgen).surjective z
    have hz : S.CentralInvolution hgen r :=
      (S.centralInvolution_iff hgen r).mpr (hr ▸ ⟨hzc,hzo⟩)
    refine ⟨C.child i r,?_⟩
    rw [← hr]
    exact (S.child_eq hgen r hz (states (C.child i r))
      (C.generator_mem i r hz) (C.lift_mem i r hz) (C.child_card i r hz)).symm

/-- Semantic acceptance is checked on the original registered states.
The registry theorem then transports it to every literal normal subgroup. -/
theorem all_normal_accepted (hG : IsPGroup 2 G)
    (Accept : Subgroup G → Prop) (haccept : ∀ i, Accept (states i).kernel)
    (N : Subgroup G) [N.Normal] : Accept N := by
  obtain ⟨i,rfl⟩ := C.complete hG N
  exact haccept i

/-- The complete registry transports through the faithful original action
without changing any literal normal subgroup or quotient kernel. -/
theorem complete_map_of_equiv {H : Type*} [Group H]
    (hG : IsPGroup 2 G) (e : G ≃* H) (N : Subgroup H) [N.Normal] :
    ∃ i, (states i).kernel.map e.toMonoidHom=N := by
  obtain ⟨i,hi⟩ := C.complete hG (N.comap e.toMonoidHom)
  refine ⟨i,?_⟩
  rw [hi,Subgroup.map_comap_eq_self_of_surjective e.surjective]

end BinaryNormalRegistry
end SymmetricSubgroupAsymptotics
