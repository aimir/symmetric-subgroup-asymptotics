import SymmetricSubgroupAsymptotics.S8Seed9LowModels
import SymmetricSubgroupAsymptotics.FiniteNormalizerPElementExtension

/-! The join of the two actual low rows contains an ordinary-word
certified larger binary subgroup. No exact join order is an input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.S8Seed9LowJoin1_4
open S8Seed9LeftCosets S8Seed9LowModels FiniteNormalizerPElementExtension

def extensionElement : Ambient where
  toFun := ![7, 1, 2, 3, 4, 6, 5, 0]
  invFun := ![7, 1, 2, 3, 4, 6, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def sourceGenerators (k : Fin 10) : Ambient :=
  Fin.addCases (m := 5) (n := 5) (S8Seed9LowModels.generators 1) (S8Seed9LowModels.generators 4) k

def normalizerCertificate : FiniteGeneratorEquivWordCertificate (MulAut.conj extensionElement)
    BinaryMenuCayley8T9.generators BinaryMenuCayley8T9.generators where
  forward := {
    words := ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.generator 3)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.generator 3)]
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
  change extensionElement ∉ Subgroup.closure (Set.range BinaryMenuCayley8T9.generators)
  rw [BinaryMenuCayley8T9.certificate.mem_closure_iff]
  decide +kernel

def inclusionWord : FiniteGeneratorWord (Fin 10) := (.mul (.mul (.generator 0) (.mul (.generator 4) (.generator 5))) (.mul (.mul (.generator 0) (.generator 5)) (.mul (.generator 4) (.generator 0))))

theorem inclusion_equation : inclusionWord.eval sourceGenerators = extensionElement := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem source_mem_join (k : Fin 10) : sourceGenerators k ∈ rows 1 ⊔ rows 4 := by
  refine Fin.addCases (m := 5) (n := 5) ?_ ?_ k
  · intro j
    simp only [sourceGenerators, Fin.addCases_left]
    exact (show rows 1 ≤ rows 1 ⊔ rows 4 from le_sup_left)
      (Subgroup.subset_closure (Set.mem_range_self j))
  · intro j
    simp only [sourceGenerators, Fin.addCases_right]
    exact (show rows 4 ≤ rows 1 ⊔ rows 4 from le_sup_right)
      (Subgroup.subset_closure (Set.mem_range_self j))

theorem element_mem_join : extensionElement ∈ rows 1 ⊔ rows 4 := by
  rw [← inclusion_equation]
  have hle : Subgroup.closure (Set.range sourceGenerators) ≤ rows 1 ⊔ rows 4 := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨k, rfl⟩
    exact source_mem_join k
  exact hle (inclusionWord.eval_mem_closure sourceGenerators)

abbrev extendedSeed : Subgroup Ambient := H ⊔ Subgroup.zpowers extensionElement

theorem extended_isPGroup : IsPGroup 2 extendedSeed :=
  extension_isPGroup H (IsPGroup.of_card (n := 4) BinaryMenuCayley8T9.exact_card)
    extensionElement 3 power_eq_one normalizes_seed

theorem extended_card_gt : 16 < Nat.card extendedSeed := by
  have h := card_lt_extension H extensionElement outside_seed
  change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T9.generators)) < _ at h
  rw [BinaryMenuCayley8T9.exact_card] at h
  exact h

theorem extended_le_join : extendedSeed ≤ rows 1 ⊔ rows 4 :=
  extension_le H _ ((seed_le 1).trans le_sup_left) extensionElement element_mem_join

end SymmetricSubgroupAsymptotics.S8Seed9LowJoin1_4
end
