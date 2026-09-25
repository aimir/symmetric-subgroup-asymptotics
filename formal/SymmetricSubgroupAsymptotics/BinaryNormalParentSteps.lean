import SymmetricSubgroupAsymptotics.BinaryNormalGeneratorChecks

/-!
# Quotient-sized normal registry installation

A child kernel is proved by two short generator-word containments against
one central-involution extension of its parent. Its normality and doubled
order are conclusions. Thus a full installation does not require an
element table for every original normal subgroup.
-/

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G ι κ : Type*} [Group G]

/-- Positive words suffice in finite groups; every checked word is an
actual product in the original source, even for nonsplit extensions. -/
structure BinaryNormalGeneratorWords (source : ι → G) (target : κ → G) where
  words : ι → List κ
  equations : ∀ i, ((words i).map target).prod=source i

namespace BinaryNormalGeneratorWords
variable {source : ι → G} {target : κ → G}
    (W : BinaryNormalGeneratorWords source target)

include W

theorem closure_le : Subgroup.closure (Set.range source) ≤
    Subgroup.closure (Set.range target) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  rw [← W.equations i]
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hg
  exact Subgroup.subset_closure ⟨j,rfl⟩

end BinaryNormalGeneratorWords

namespace BinaryNormalState
variable [Finite G] {generators : ι → G}
    (S : BinaryNormalState generators)
    (hgen : Subgroup.closure (Set.range generators)=⊤)

/-- The linear-sized row test is also sufficient: commuting with the
retained generating tuple is equivalent to centrality in the whole quotient. -/
theorem centralRowTests_iff (z : S.Row) :
    S.centralRowTests hgen z ↔ S.CentralInvolution hgen z := by
  letI := S.group hgen
  refine ⟨?_,S.centralInvolution_rowTests hgen z⟩
  rintro ⟨hne,hsq,hcomm⟩
  refine ⟨?_,(orderOf_eq_prime_iff (p := 2)).mpr ⟨by simpa only [pow_two] using hsq,hne⟩⟩
  have hf : Subgroup.closure (Set.range (fun j =>
      (⟨S.cosets.next S.cosets.identity j⟩ : S.Row)))=⊤ :=
    (S.cosets.toEncoded hgen S.cardinal).row_generators_full
      Function.injective_id S.prev S.prev_next
  rw [Subgroup.center_eq_iInf hf]
  simp only [Subgroup.mem_iInf,Set.mem_range,forall_exists_index,forall_apply_eq_imp_iff]
  intro j
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hcomm j

/-- Append the selected original lift to the parent's original tuple. -/
def extensionGenerators (z : S.Row) : Fin S.generatorCount ⊕ Unit → G :=
  Sum.elim S.normalGenerators (fun _ => S.cosets.representatives z.index)

omit [Finite G] in
theorem extensionGenerators_closure (z : S.Row) :
    Subgroup.closure (Set.range (S.extensionGenerators z))=
      S.kernel ⊔ Subgroup.zpowers (S.cosets.representatives z.index) := by
  have hr : Set.range (S.extensionGenerators z)=Set.range S.normalGenerators ∪
      {S.cosets.representatives z.index} := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      cases i with
      | inl j => exact Or.inl ⟨j,rfl⟩
      | inr j => exact Or.inr rfl
    · rintro (⟨j,rfl⟩ | rfl)
      · exact ⟨Sum.inl j,rfl⟩
      · exact ⟨Sum.inr (),rfl⟩
  rw [hr,Subgroup.closure_union,S.generated,Subgroup.zpowers_eq_closure]

end BinaryNormalState

/-- Two checked generator-word maps identify a literal child with its
actual parent extension. The recorded row is checked central of order two. -/
structure BinaryNormalParentStep [Finite G] {generators : ι → G}
    (hgen : Subgroup.closure (Set.range generators)=⊤)
    (S : BinaryNormalState generators) (childGenerators : κ → G) where
  row : S.Row
  central : S.centralRowTests hgen row
  child_in_extension : BinaryNormalGeneratorWords childGenerators (S.extensionGenerators row)
  extension_in_child : BinaryNormalGeneratorWords (S.extensionGenerators row) childGenerators

namespace BinaryNormalParentStep
variable [Finite G] {generators : ι → G}
    {hgen : Subgroup.closure (Set.range generators)=⊤}
    {S : BinaryNormalState generators} {childGenerators : κ → G}
    (E : BinaryNormalParentStep hgen S childGenerators)

include E

/-- The actual child is the quotient cyclic preimage, including its
original extension and its original higher-order lift. -/
theorem kernel_eq : Subgroup.closure (Set.range childGenerators)=
    (Subgroup.zpowers (S.quotientEquiv hgen E.row)).comap
      (QuotientGroup.mk' S.kernel) := by
  have he : Subgroup.closure (Set.range childGenerators)=
      Subgroup.closure (Set.range (S.extensionGenerators E.row)) :=
    le_antisymm E.child_in_extension.closure_le E.extension_in_child.closure_le
  rw [he,S.extensionGenerators_closure]
  have hr : S.quotientEquiv hgen E.row=
      QuotientGroup.mk' S.kernel (S.cosets.representatives E.row.index) :=
    S.cosets.rowQuotientEquiv_apply hgen S.cardinal S.prev S.prev_next E.row
  rw [hr,normal_step_generated]

/-- Normality follows from the original quotient's central-involution check. -/
theorem normal : (Subgroup.closure (Set.range childGenerators)).Normal := by
  have hz := (S.centralInvolution_iff hgen E.row).mp
    ((S.centralRowTests_iff hgen E.row).mp E.central)
  rw [E.kernel_eq]
  exact (central_prime_preimage_properties (p := 2) S.kernel _ hz.1 hz.2).1

/-- No declared normal order is trusted: the original child order doubles. -/
theorem cardinal : Nat.card (Subgroup.closure (Set.range childGenerators))=
    Nat.card S.kernel*2 := by
  rw [E.kernel_eq]
  have hz := (S.centralInvolution_iff hgen E.row).mp
    ((S.centralRowTests_iff hgen E.row).mp E.central)
  have hr : S.quotientEquiv hgen E.row=
      QuotientGroup.mk' S.kernel (S.cosets.representatives E.row.index) :=
    S.cosets.rowQuotientEquiv_apply hgen S.cardinal S.prev S.prev_next E.row
  rw [hr] at hz ⊢
  rw [normal_step_card,hz.2]

/-- Install a child state using quotient-sized rows alone. The original
kernel order is proved from its parent extension, rather than accepted from
the producer or established by enumerating every child element. -/
def toState {r q : ℕ} {childGenerators : Fin r → G}
    (E : BinaryNormalParentStep hgen S childGenerators)
    (hquotient : S.quotientCount=2*q)
    (C : letI := E.normal
      BinaryNormalCosetCertificate generators (Subgroup.closure (Set.range childGenerators)) q)
    (prev : Fin q → ι → Fin q) (hprev : letI := E.normal
      ∀ i j, C.next (prev i j) j=i) :
    BinaryNormalState generators := by
  letI := E.normal
  exact {
  kernel := Subgroup.closure (Set.range childGenerators)
  normal := E.normal
  generatorCount := r
  normalGenerators := childGenerators
  generated := rfl
  quotientCount := q
  cardinal := by
    rw [E.cardinal,Nat.mul_assoc,← hquotient]
    exact S.cardinal
  cosets := C
  prev := prev
  prev_next := hprev }

end BinaryNormalParentStep
end SymmetricSubgroupAsymptotics
