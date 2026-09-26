import SymmetricSubgroupAsymptotics.BinaryGeneratorWords

/-! Relative normality from literal generator conjugates in a finite
ambient group. Only forward conjugates of lower generators by upper
generators are checked. Finiteness supplies inverse preservation, and
closure supplies all words. No multiplication table is required. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G ι κ : Type*} [Group G] [Finite G]

/-- Forward conjugates of the lower generators suffice to show that the
whole upper generated subgroup normalizes the whole lower subgroup. -/
theorem generated_le_normalizer_of_generator_conjugates
    (lower : κ → G) (upper : ι → G)
    (hconj : ∀ i j, upper i * lower j * (upper i)⁻¹ ∈
      Subgroup.closure (Set.range lower)) :
    Subgroup.closure (Set.range upper) ≤
      Subgroup.normalizer (Subgroup.closure (Set.range lower) : Set G) := by
  let L := Subgroup.closure (Set.range lower)
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  have hpres : L ≤ L.comap (MulAut.conj (upper i)).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    exact hconj i j
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  exact hpres hx

/-- A composition-chain step retains its literal lower and upper
closures. The inclusion premise is explicit and normality concerns the
lower subgroup inside that actual upper subgroup. -/
theorem generated_subgroupOf_normal_of_generator_conjugates
    (lower : κ → G) (upper : ι → G)
    (hle : Subgroup.closure (Set.range lower) ≤ Subgroup.closure (Set.range upper))
    (hconj : ∀ i j, upper i * lower j * (upper i)⁻¹ ∈
      Subgroup.closure (Set.range lower)) :
    ((Subgroup.closure (Set.range lower)).subgroupOf
      (Subgroup.closure (Set.range upper))).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
    (generated_le_normalizer_of_generator_conjugates lower upper hconj)

/-- Short original-generator words certify each conjugate. Their products
are evaluated in the original ambient group, not in an unrelated row group. -/
theorem generated_subgroupOf_normal_of_conjugate_words
    (lower : κ → G) (upper : ι → G)
    (hle : Subgroup.closure (Set.range lower) ≤ Subgroup.closure (Set.range upper))
    (words : ι → κ → List κ)
    (hwords : ∀ i j, ((words i j).map lower).prod =
      upper i * lower j * (upper i)⁻¹) :
    ((Subgroup.closure (Set.range lower)).subgroupOf
      (Subgroup.closure (Set.range upper))).Normal := by
  apply generated_subgroupOf_normal_of_generator_conjugates lower upper hle
  intro i j
  rw [← hwords i j]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
  exact Subgroup.subset_closure (Set.mem_range_self k)

/-- Existing literal word certificates can supply both chain containment
and conjugation closure. Only generator-pair conjugates are listed. -/
theorem generated_subgroupOf_normal_of_word_certificates
    (lower : κ → G) (upper : ι → G)
    (inclusionWords : BinaryNormalGeneratorWords lower upper)
    (conjugateWords : BinaryNormalGeneratorWords
      (fun ij : ι × κ => upper ij.1 * lower ij.2 * (upper ij.1)⁻¹) lower) :
    ((Subgroup.closure (Set.range lower)).subgroupOf
      (Subgroup.closure (Set.range upper))).Normal := by
  apply generated_subgroupOf_normal_of_generator_conjugates lower upper
    inclusionWords.closure_le
  intro i j
  exact conjugateWords.closure_le
    (Subgroup.subset_closure (Set.mem_range_self (i, j)))

end SymmetricSubgroupAsymptotics
