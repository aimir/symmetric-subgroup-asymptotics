import SymmetricSubgroupAsymptotics.S8Seed8LowModels
import SymmetricSubgroupAsymptotics.FiniteNormalizerPElementExtension

/-! The join of the two actual low rows contains an ordinary-word
certified larger binary subgroup. No exact join order is an input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.S8Seed8LowJoinEscape
open S8Seed8LeftCosets S8Seed8LowModels FiniteNormalizerPElementExtension

def extensionElement : Ambient where
  toFun := ![4, 3, 2, 1, 0, 7, 6, 5]
  invFun := ![4, 3, 2, 1, 0, 7, 6, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def sourceGenerators (k : Fin 6) : Ambient :=
  Fin.addCases (m := 3) (n := 3) (S8Seed8LowModels.generators 1) (S8Seed8LowModels.generators 2) k

def normalizerCertificate : FiniteGeneratorEquivWordCertificate (MulAut.conj extensionElement)
    BinaryMenuCayley8T8.generators BinaryMenuCayley8T8.generators where
  forward := {
    words := ![(.inv (.generator 0)), (.mul (.generator 0) (.mul (.generator 1) (.generator 0)))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.inv (.generator 0)), (.mul (.generator 0) (.mul (.generator 1) (.generator 0)))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem normalizes_seed : extensionElement ∈ Subgroup.normalizer H := by
  apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
  exact congrArg (fun K : Subgroup Ambient => (K : Set Ambient))
    normalizerCertificate.map_closure_eq

theorem power_eq_one : extensionElement ^ (2 ^ 3) = 1 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem outside_seed : extensionElement ∉ H := by
  change extensionElement ∉ Subgroup.closure (Set.range BinaryMenuCayley8T8.generators)
  rw [BinaryMenuCayley8T8.certificate.mem_closure_iff]
  decide +kernel

def inclusionWord : FiniteGeneratorWord (Fin 6) := (.mul (.generator 0) (.mul (.generator 3) (.generator 0)))

theorem inclusion_equation : inclusionWord.eval sourceGenerators = extensionElement := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem source_mem_join (k : Fin 6) : sourceGenerators k ∈ rows 1 ⊔ rows 2 := by
  refine Fin.addCases (m := 3) (n := 3) ?_ ?_ k
  · intro j
    simp only [sourceGenerators, Fin.addCases_left]
    exact (show rows 1 ≤ rows 1 ⊔ rows 2 from le_sup_left)
      (Subgroup.subset_closure (Set.mem_range_self j))
  · intro j
    simp only [sourceGenerators, Fin.addCases_right]
    exact (show rows 2 ≤ rows 1 ⊔ rows 2 from le_sup_right)
      (Subgroup.subset_closure (Set.mem_range_self j))

theorem element_mem_join : extensionElement ∈ rows 1 ⊔ rows 2 := by
  rw [← inclusion_equation]
  have hle : Subgroup.closure (Set.range sourceGenerators) ≤ rows 1 ⊔ rows 2 := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨k, rfl⟩
    exact source_mem_join k
  exact hle (inclusionWord.eval_mem_closure sourceGenerators)

abbrev extendedSeed : Subgroup Ambient := H ⊔ Subgroup.zpowers extensionElement

theorem extended_isPGroup : IsPGroup 2 extendedSeed :=
  extension_isPGroup H (IsPGroup.of_card (n := 4) BinaryMenuCayley8T8.exact_card)
    extensionElement 3 power_eq_one normalizes_seed

theorem extended_card_gt : 16 < Nat.card extendedSeed := by
  have h := card_lt_extension H extensionElement outside_seed
  change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T8.generators)) < _ at h
  rw [BinaryMenuCayley8T8.exact_card] at h
  exact h

theorem extended_le_join : extendedSeed ≤ rows 1 ⊔ rows 2 :=
  extension_le H _ ((seed_le 1).trans le_sup_left) extensionElement element_mem_join

end SymmetricSubgroupAsymptotics.S8Seed8LowJoinEscape
end
