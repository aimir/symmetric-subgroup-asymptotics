import SymmetricSubgroupAsymptotics.S8Seed18NormalizerRoots
import SymmetricSubgroupAsymptotics.FiniteNormalizerPElementExtension
import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate
import Mathlib.Tactic.FinCases

/-! One actual larger binary extension inside a selected adjunction.
Only ordinary words, a literal power equation, seed nonmembership and
normalizer equations are checked. No abstract row correspondence is input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.S8Seed18Root3BinaryExtension
open S8Seed18LeftCosets FiniteNormalizerPElementExtension

def extensionElement : Ambient where
  toFun := ![4, 6, 5, 0, 7, 1, 2, 3]
  invFun := ![3, 5, 6, 7, 0, 2, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def sourceGenerators : Fin 6 → Ambient :=
  Matrix.vecCons (representatives (S8Seed18NormalizerRoots.roots 3))
    BinaryMenuCayley8T18.generators

def normalizerCertificate : FiniteGeneratorEquivWordCertificate (MulAut.conj extensionElement)
    BinaryMenuCayley8T18.generators BinaryMenuCayley8T18.generators where
  forward := {
    words := ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.mul (.generator 0) (.generator 3)), (.mul (.mul (.generator 0) (.generator 1)) (.mul (.generator 3) (.generator 4)))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.mul (.generator 0) (.generator 3)), (.mul (.mul (.generator 0) (.generator 1)) (.mul (.generator 3) (.generator 4)))]
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

set_option maxHeartbeats 1000000 in
theorem outside_seed : extensionElement ∉ H := by
  change extensionElement ∉ Subgroup.closure (Set.range BinaryMenuCayley8T18.generators)
  rw [BinaryMenuCayley8T18.certificate.mem_closure_iff]
  decide +kernel

def inclusionWord : FiniteGeneratorWord (Fin 6) := (.mul (.generator 0) (.mul (.generator 4) (.generator 0)))

theorem inclusion_equation : inclusionWord.eval sourceGenerators = extensionElement := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem element_mem_adjoin : extensionElement ∈
    (H ⊔ Subgroup.closure {representatives (S8Seed18NormalizerRoots.roots 3)} : Subgroup Ambient) := by
  rw [← inclusion_equation]
  have h := inclusionWord.eval_mem_closure sourceGenerators
  simpa only [sourceGenerators, Matrix.range_cons, Subgroup.closure_union, sup_comm] using h

abbrev extendedSeed : Subgroup Ambient := H ⊔ Subgroup.zpowers extensionElement

theorem extended_isPGroup : IsPGroup 2 extendedSeed :=
  extension_isPGroup H (IsPGroup.of_card (n := 5) BinaryMenuCayley8T18.exact_card)
    extensionElement 3 power_eq_one normalizes_seed

theorem extended_card_gt : 32 < Nat.card extendedSeed := by
  have h := card_lt_extension H extensionElement outside_seed
  change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T18.generators)) < _ at h
  rw [BinaryMenuCayley8T18.exact_card] at h
  exact h

theorem extended_le_adjoin : extendedSeed ≤
    H ⊔ Subgroup.closure {representatives (S8Seed18NormalizerRoots.roots 3)} :=
  extension_le H _ le_sup_left extensionElement element_mem_adjoin

end SymmetricSubgroupAsymptotics.S8Seed18Root3BinaryExtension
end
