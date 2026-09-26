import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T27
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T28
import SymmetricSubgroupAsymptotics.FiniteCayleyMaps

/-! A fixed epimorphism from the literal original 8T27 closure to the literal
original 8T28 closure. The source images are in the checked Lean generator
order (the reverse of the two-generator order in carrier_master_maps.json).
Only the existing 64 source rows and three target-generator preimages are
checked. No target action conjugacy or normalizer identification is asserted. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierEpimorphism8T27To28

abbrev Source := Subgroup.closure (Set.range BinaryMenuCayley8T27.generators)
abbrev Target := Subgroup.closure (Set.range BinaryMenuCayley8T28.generators)

private def image0 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,5,0,7,6,1,4,3] : Array (Fin 8))[x.val]!
  invFun x := (#[2,5,0,7,6,1,4,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def image1 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,6,1,0,7,2,5,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,2,5,0,7,6,1,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Images of the complete original ordered source tuple. -/
def images (j : Fin 2) : Equiv.Perm (Fin 8) :=
  if j.val = 0 then image0 else image1

/-- Evaluate only the already certified source parent word. -/
def values (i : Fin 64) : Equiv.Perm (Fin 8) :=
  ((BinaryMenuCayley8T27.certificate.words i).map images).prod

private theorem images_mem : ∀ j : Fin 2, images j ∈ Target := by
  intro j
  apply (BinaryMenuCayley8T28.certificate.mem_closure_iff (images j)).mpr
  exact (by
    decide +kernel :
    ∀ j : Fin 2, ∃ i : Fin 64,
      BinaryMenuCayley8T28.certificate.rows i = permutationCode (images j)) j

private theorem values_mem (i : Fin 64) : values i ∈ Target := by
  apply Subgroup.list_prod_mem
  intro y hy
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
  exact images_mem j

private theorem values_identity :
    values BinaryMenuCayley8T27.certificate.identity = 1 := by
  simp only [values, EncodedCayleyCertificate.words_identity,
    List.map_nil, List.prod_nil]

private theorem transition_0 :
    ∀ i : Fin 8, ∀ j : Fin 2, ∀ x : Fin 8,
      values (BinaryMenuCayley8T27.certificate.next
        ⟨0 + i.val, by omega⟩ j) x =
      (values ⟨0 + i.val, by omega⟩ * images j) x := by
  decide +kernel

private theorem transition_1 :
    ∀ i : Fin 8, ∀ j : Fin 2, ∀ x : Fin 8,
      values (BinaryMenuCayley8T27.certificate.next
        ⟨8 + i.val, by omega⟩ j) x =
      (values ⟨8 + i.val, by omega⟩ * images j) x := by
  decide +kernel

private theorem transition_2 :
    ∀ i : Fin 8, ∀ j : Fin 2, ∀ x : Fin 8,
      values (BinaryMenuCayley8T27.certificate.next
        ⟨16 + i.val, by omega⟩ j) x =
      (values ⟨16 + i.val, by omega⟩ * images j) x := by
  decide +kernel

private theorem transition_3 :
    ∀ i : Fin 8, ∀ j : Fin 2, ∀ x : Fin 8,
      values (BinaryMenuCayley8T27.certificate.next
        ⟨24 + i.val, by omega⟩ j) x =
      (values ⟨24 + i.val, by omega⟩ * images j) x := by
  decide +kernel

private theorem transition_4 :
    ∀ i : Fin 8, ∀ j : Fin 2, ∀ x : Fin 8,
      values (BinaryMenuCayley8T27.certificate.next
        ⟨32 + i.val, by omega⟩ j) x =
      (values ⟨32 + i.val, by omega⟩ * images j) x := by
  decide +kernel

private theorem transition_5 :
    ∀ i : Fin 8, ∀ j : Fin 2, ∀ x : Fin 8,
      values (BinaryMenuCayley8T27.certificate.next
        ⟨40 + i.val, by omega⟩ j) x =
      (values ⟨40 + i.val, by omega⟩ * images j) x := by
  decide +kernel

private theorem transition_6 :
    ∀ i : Fin 8, ∀ j : Fin 2, ∀ x : Fin 8,
      values (BinaryMenuCayley8T27.certificate.next
        ⟨48 + i.val, by omega⟩ j) x =
      (values ⟨48 + i.val, by omega⟩ * images j) x := by
  decide +kernel

private theorem transition_7 :
    ∀ i : Fin 8, ∀ j : Fin 2, ∀ x : Fin 8,
      values (BinaryMenuCayley8T27.certificate.next
        ⟨56 + i.val, by omega⟩ j) x =
      (values ⟨56 + i.val, by omega⟩ * images j) x := by
  decide +kernel

private theorem transitions (i : Fin 64) (j : Fin 2) :
    values (BinaryMenuCayley8T27.certificate.next i j) = values i * images j := by
  apply Equiv.ext
  intro x
  by_cases h0 : i.val < 8
  · have hi : (⟨0 + (i.val - 0), by omega⟩ : Fin 64) = i := by
      apply Fin.ext
      change 0 + (i.val - 0) = i.val
      omega
    simpa only [hi] using transition_0 ⟨i.val - 0, by omega⟩ j x
  by_cases h1 : i.val < 16
  · have hi : (⟨8 + (i.val - 8), by omega⟩ : Fin 64) = i := by
      apply Fin.ext
      change 8 + (i.val - 8) = i.val
      omega
    simpa only [hi] using transition_1 ⟨i.val - 8, by omega⟩ j x
  by_cases h2 : i.val < 24
  · have hi : (⟨16 + (i.val - 16), by omega⟩ : Fin 64) = i := by
      apply Fin.ext
      change 16 + (i.val - 16) = i.val
      omega
    simpa only [hi] using transition_2 ⟨i.val - 16, by omega⟩ j x
  by_cases h3 : i.val < 32
  · have hi : (⟨24 + (i.val - 24), by omega⟩ : Fin 64) = i := by
      apply Fin.ext
      change 24 + (i.val - 24) = i.val
      omega
    simpa only [hi] using transition_3 ⟨i.val - 24, by omega⟩ j x
  by_cases h4 : i.val < 40
  · have hi : (⟨32 + (i.val - 32), by omega⟩ : Fin 64) = i := by
      apply Fin.ext
      change 32 + (i.val - 32) = i.val
      omega
    simpa only [hi] using transition_4 ⟨i.val - 32, by omega⟩ j x
  by_cases h5 : i.val < 48
  · have hi : (⟨40 + (i.val - 40), by omega⟩ : Fin 64) = i := by
      apply Fin.ext
      change 40 + (i.val - 40) = i.val
      omega
    simpa only [hi] using transition_5 ⟨i.val - 40, by omega⟩ j x
  by_cases h6 : i.val < 56
  · have hi : (⟨48 + (i.val - 48), by omega⟩ : Fin 64) = i := by
      apply Fin.ext
      change 48 + (i.val - 48) = i.val
      omega
    simpa only [hi] using transition_6 ⟨i.val - 48, by omega⟩ j x
  have hi : (⟨56 + (i.val - 56), by omega⟩ : Fin 64) = i := by
    apply Fin.ext
    change 56 + (i.val - 56) = i.val
    omega
  simpa only [hi] using transition_7 ⟨i.val - 56, by omega⟩ j x

local instance : Group (FiniteGroupRow 64) := BinaryMenuCayley8T27.group

/-- The existing generator-transition theorem supplies the group law. -/
private def rowHom : FiniteGroupRow 64 →* Equiv.Perm (Fin 8) where
  toFun i := values i.index
  map_one' := values_identity
  map_mul' i j := by
    change values (BinaryMenuCayley8T27.certificate.walk i.index
      (BinaryMenuCayley8T27.certificate.words j.index)) = values i.index * values j.index
    exact BinaryMenuCayley8T27.certificate.values_walk values images transitions
      i.index (BinaryMenuCayley8T27.certificate.words j.index)

private def permutationHom : Source →* Equiv.Perm (Fin 8) :=
  rowHom.comp BinaryMenuCayley8T27.originalEquiv.symm.toMonoidHom

private theorem permutationHom_row (i : Fin 64) :
    permutationHom (BinaryMenuCayley8T27.originalEquiv ⟨i⟩) = values i := by
  change rowHom (BinaryMenuCayley8T27.originalEquiv.symm
    (BinaryMenuCayley8T27.originalEquiv ⟨i⟩)) = values i
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The actual epimorphism has the original target closure as codomain. -/
def hom : Source →* Target :=
  permutationHom.codRestrict Target (fun x =>
    values_mem (BinaryMenuCayley8T27.originalEquiv.symm x).index)

@[simp] theorem hom_row (i : Fin 64) :
    (hom (BinaryMenuCayley8T27.originalEquiv ⟨i⟩) : Equiv.Perm (Fin 8)) = values i :=
  permutationHom_row i

/-- Exact images of the original source generators, in their original order. -/
theorem hom_generator (j : Fin 2) :
    (hom ⟨BinaryMenuCayley8T27.generators j,
      Subgroup.subset_closure (Set.mem_range_self j)⟩ : Equiv.Perm (Fin 8)) =
      images j := by
  have he : BinaryMenuCayley8T27.originalEquiv
      ⟨BinaryMenuCayley8T27.certificate.next
        BinaryMenuCayley8T27.certificate.identity j⟩ =
      (⟨BinaryMenuCayley8T27.generators j,
        Subgroup.subset_closure (Set.mem_range_self j)⟩ : Source) := by
    apply Subtype.ext
    change BinaryMenuCayley8T27.certificate.toCayley.elements
      (BinaryMenuCayley8T27.certificate.toCayley.next
        BinaryMenuCayley8T27.certificate.toCayley.identity j) = _
    rw [BinaryMenuCayley8T27.certificate.toCayley.next_eq,
      BinaryMenuCayley8T27.certificate.toCayley.identity_eq, one_mul]
  rw [← he, hom_row, transitions, values_identity, one_mul]

/-- A finite check of three original target generators, not a claim that an
abstract isomorphism conjugates the two permutation actions. -/
private theorem target_generator_preimages :
    ∀ j : Fin 3, ∃ i : Fin 64, ∀ x : Fin 8,
      values i x = BinaryMenuCayley8T28.generators j x := by
  decide +kernel

theorem hom_surjective : Function.Surjective hom := by
  have hrange : Target ≤ permutationHom.range := by
    apply (Subgroup.closure_le _).mpr
    rintro y ⟨j, rfl⟩
    obtain ⟨i, hi⟩ := target_generator_preimages j
    refine ⟨BinaryMenuCayley8T27.originalEquiv ⟨i⟩, ?_⟩
    exact (permutationHom_row i).trans (Equiv.ext hi)
  intro y
  obtain ⟨x, hx⟩ := hrange y.property
  exact ⟨x, Subtype.ext hx⟩

end SymmetricSubgroupAsymptotics.BinaryCarrierEpimorphism8T27To28
