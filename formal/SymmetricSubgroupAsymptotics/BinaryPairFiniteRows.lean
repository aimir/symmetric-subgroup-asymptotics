import SymmetricSubgroupAsymptotics.BinaryNormalParentSteps
import SymmetricSubgroupAsymptotics.BinaryPairFixedCertificates

/-! Finite row checks for literal pair cuts and their complete fixed
preimages. Kernels, cuts and source generators are actual group objects. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

/-- Membership in a reflected normal/cut table is an exact finite row test. -/
theorem binaryNormalRow_mem_iff {n k : ℕ} {ι : Type*} [Group (FiniteGroupRow n)]
    {generators : ι → FiniteGroupRow n}
    (C : EncodedCayleyCertificate (binaryNormalRowEncoding generators) k)
    (x : FiniteGroupRow n) :
    x∈Subgroup.closure (Set.range generators) ↔ ∃ i, C.rows i=x.index := by
  rw [C.toCayley.mem_closure_iff]
  constructor
  · rintro ⟨i,hi⟩
    refine ⟨i,?_⟩
    rw [← C.encode_elements]
    exact congrArg FiniteGroupRow.index hi
  · rintro ⟨i,hi⟩
    refine ⟨i,?_⟩
    rw [binaryNormalRow_elements]
    exact FiniteGroupRow.ext hi

variable {G ι : Type*} [Group G]

/-- Exact fixed preimage inside the literal original pair kernel. -/
def binaryPairFixedSubgroup (K C : Subgroup G) [C.Normal] : Subgroup G :=
  K ⊓ (Subgroup.center (G ⧸ C)).comap (QuotientGroup.mk' C)

/-- Centrality modulo the actual cut is checked on original generators. -/
theorem binaryPair_quotient_center_iff (C : Subgroup G) [C.Normal]
    (generators : ι → G) (hgen : Subgroup.closure (Set.range generators)=⊤) (x : G) :
    QuotientGroup.mk' C x∈Subgroup.center (G ⧸ C) ↔
      ∀ j, x⁻¹*(generators j*x*(generators j)⁻¹)∈C := by
  rw [Subgroup.center_eq_iInf (BinaryNormalCosetCertificate.quotient_generators_full (N := C) hgen)]
  simp only [Subgroup.mem_iInf,Set.mem_range,forall_exists_index,forall_apply_eq_imp_iff,
    Subgroup.mem_centralizer_singleton_iff]
  apply forall_congr'
  intro j
  rw [← QuotientGroup.eq_one_iff (x⁻¹*(generators j*x*(generators j)⁻¹))]
  change (QuotientGroup.mk' C x*QuotientGroup.mk' C (generators j)=
    QuotientGroup.mk' C (generators j)*QuotientGroup.mk' C x) ↔
      QuotientGroup.mk' C (x⁻¹*(generators j*x*(generators j)⁻¹))=1
  simp only [map_mul,map_inv]
  rw [inv_mul_eq_one, eq_mul_inv_iff_mul_eq]

theorem binaryPairFixedSubgroup_mem_iff (K C : Subgroup G) [C.Normal]
    (generators : ι → G) (hgen : Subgroup.closure (Set.range generators)=⊤) (x : G) :
    x∈binaryPairFixedSubgroup K C ↔
      x∈K ∧ ∀ j, x⁻¹*(generators j*x*(generators j)⁻¹)∈C := by
  exact and_congr_right (fun _ => binaryPair_quotient_center_iff C generators hgen x)

/-- A finite characteristic row predicate counts an actual subgroup.
The equivalence must be proved from its original group membership. -/
theorem binaryPair_card_of_row_predicate {n : ℕ} [Group (FiniteGroupRow n)]
    (H : Subgroup (FiniteGroupRow n)) (P : Fin n → Prop) [DecidablePred P]
    (hP : ∀ x : FiniteGroupRow n, x∈H ↔ P x.index) :
    Nat.card H=Fintype.card {i : Fin n // P i} := by
  let e : H ≃ {i : Fin n // P i} := {
    toFun x := ⟨x.val.index,(hP x.val).mp x.property⟩
    invFun i := ⟨⟨i.val⟩,(hP ⟨i.val⟩).mpr i.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card]

/-- The complete local group-theoretic content of a pair certificate.
All subgroup orders and maps concern this original source; no capacity or
whole-family counting bound is a field of the certificate. -/
structure BinaryPairLocalCertificate (generators : ι → G)
    {I : Type*} (top : G →* Equiv.Perm I) (N : Subgroup G) where
  cut : Subgroup G
  cut_normal : cut.Normal
  cut_le_kernel : cut≤top.ker
  intersection_le_cut : top.ker⊓N≤cut
  central : ∀ j, ∀ x : cut, (x:G)⁻¹*(generators j*(x:G)*(generators j)⁻¹)∈N
  cutDimension : ℕ
  fixedDimension : ℕ
  cut_card : Nat.card cut=Nat.card ↥(top.ker⊓N)*2^cutDimension
  fixed_card : letI := cut_normal
    Nat.card (binaryPairFixedSubgroup top.ker cut)=Nat.card cut*2^fixedDimension
  coverDegree : ℕ
  cover : G →* Equiv.Perm (Fin coverDegree)
  cover_kernel : cover.ker=top.ker⊔N
  width : ℕ
  gap : coverDegree+2*cutDimension+4*fixedDimension<width

end SymmetricSubgroupAsymptotics
