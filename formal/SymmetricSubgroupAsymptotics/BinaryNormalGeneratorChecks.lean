import SymmetricSubgroupAsymptotics.BinaryNormalRegistry
import SymmetricSubgroupAsymptotics.BinaryGeneratorWords

/-! Generator checks for literal normal-state certificates. -/

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G ι κ : Type*} [Group G]

/-- To prove a literal generated subgroup normal it suffices to check
conjugation of its generators by the original generators and their inverses. -/
theorem binaryNormal_of_generator_conjugates
    (generators : ι → G) (hgen : Subgroup.closure (Set.range generators)=⊤)
    (normalGenerators : κ → G)
    (hpos : ∀ i j, generators i*normalGenerators j*(generators i)⁻¹ ∈
      Subgroup.closure (Set.range normalGenerators))
    (hneg : ∀ i j, (generators i)⁻¹*normalGenerators j*generators i ∈
      Subgroup.closure (Set.range normalGenerators)) :
    (Subgroup.closure (Set.range normalGenerators)).Normal := by
  let N := Subgroup.closure (Set.range normalGenerators)
  have hconj : ∀ i, N ≤ N.comap (MulAut.conj (generators i)).toMonoidHom := by
    intro i
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact hpos i j
  have hinv : ∀ i, N ≤ N.comap (MulAut.conj ((generators i)⁻¹)).toMonoidHom := by
    intro i
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    simpa using hneg i j
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  change generators i ∈ Subgroup.normalizer (N : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    simpa only [Subgroup.mem_comap, MulEquiv.toMonoidHom_eq_coe, MulAut.conj_apply] using hconj i hx
  · intro hx
    have hh := hinv i hx
    simpa [Subgroup.mem_comap, MulAut.conj_apply, mul_assoc] using hh


namespace EncodedCayleyCertificate

variable [Finite G] {Code : Type*} {generators : ι → G}
    {E : GeneratorEncoding generators Code} {n : ℕ}
    (C : EncodedCayleyCertificate E n)
    (hinj : Function.Injective C.rows)
    (prev : Fin n → ι → Fin n) (hprev : ∀ i j, C.next (prev i j) j=i)

/-- The original generator rows generate the entire faithful row group. -/
theorem row_generators_full :
    letI := C.rowGroup hinj prev hprev
    Subgroup.closure (Set.range (fun j =>
      (⟨C.next C.identity j⟩ : FiniteGroupRow n)))=⊤ := by
  letI := C.rowGroup hinj prev hprev
  let f := C.rowHom hinj prev hprev
  have hf : Function.Injective f := C.rowHom_injective hinj prev hprev
  have hm : (Subgroup.closure (Set.range (fun j =>
      (⟨C.next C.identity j⟩ : FiniteGroupRow n)))).map f=f.range := by
    rw [MonoidHom.map_closure,C.rowHom_range]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_range,exists_exists_eq_and]
    have hh : ∀ j, f ⟨C.next C.identity j⟩=generators j := by
      intro j
      change C.toCayley.elements (C.next C.identity j)=_
      rw [show C.next=C.toCayley.next from rfl,C.toCayley.next_eq,
        show C.identity=C.toCayley.identity from rfl,C.toCayley.identity_eq,one_mul]
    simp only [hh]
  apply Subgroup.map_injective hf
  simpa only [MonoidHom.range_eq_map] using hm

end EncodedCayleyCertificate

/-- Faithful row-index encoding for a normal subgroup's own Cayley table. -/
def binaryNormalRowEncoding {n : ℕ} [Group (FiniteGroupRow n)]
    (generators : ι → FiniteGroupRow n) :
    GeneratorEncoding generators (Fin n) where
  encode := FiniteGroupRow.index
  injective := fun _ _ => FiniteGroupRow.ext
  one := (1 : FiniteGroupRow n).index
  encode_one := rfl
  step i j := ((⟨i⟩ : FiniteGroupRow n)*generators j).index
  encode_step _ _ := rfl

/-- A normal-table row is the literal original source row, not a fresh
unrelated finite group element. -/
theorem binaryNormalRow_elements {n k : ℕ} [Group (FiniteGroupRow n)]
    {generators : ι → FiniteGroupRow n}
    (C : EncodedCayleyCertificate (binaryNormalRowEncoding generators) k)
    (i : Fin k) : C.toCayley.elements i=⟨C.rows i⟩ := by
  apply FiniteGroupRow.ext
  exact C.encode_elements i

theorem binaryNormalRow_mem {n k : ℕ} [Group (FiniteGroupRow n)]
    {generators : ι → FiniteGroupRow n}
    (C : EncodedCayleyCertificate (binaryNormalRowEncoding generators) k)
    (i : Fin k) : (⟨C.rows i⟩ : FiniteGroupRow n)∈Subgroup.closure (Set.range generators) := by
  rw [← binaryNormalRow_elements C i]
  exact (C.toCayley.mem_closure_iff _).mpr ⟨i,rfl⟩

end SymmetricSubgroupAsymptotics
