import SymmetricSubgroupAsymptotics.S8Seed20NormalizerRoots
import SymmetricSubgroupAsymptotics.FiniteNormalizerPElementExtension
import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate
import Mathlib.Tactic.FinCases

/-! One actual larger binary extension inside a selected adjunction.
Only ordinary words, a literal power equation, seed nonmembership and
normalizer equations are checked. No abstract row correspondence is input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.S8Seed20Root30BinaryExtension
open S8Seed20LeftCosets FiniteNormalizerPElementExtension

def extensionElement : Ambient where
  toFun := ![2, 1, 4, 7, 6, 5, 0, 3]
  invFun := ![6, 1, 0, 7, 2, 5, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def sourceGenerators : Fin 3 → Ambient :=
  Matrix.vecCons (representatives (S8Seed20NormalizerRoots.roots 30))
    BinaryMenuCayley8T20.generators

def normalizerCertificate : FiniteGeneratorEquivWordCertificate (MulAut.conj extensionElement)
    BinaryMenuCayley8T20.generators BinaryMenuCayley8T20.generators where
  forward := {
    words := ![(.mul (.inv (.generator 1)) (.mul (.generator 0) (.generator 1))), (.mul (.generator 0) (.mul (.inv (.generator 1)) (.generator 0)))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.inv (.generator 1)) (.mul (.generator 0) (.generator 1))), (.mul (.mul (.generator 0) (.generator 1)) (.mul (.generator 0) (.mul (.generator 1) (.generator 1))))]
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
  change extensionElement ∉ Subgroup.closure (Set.range BinaryMenuCayley8T20.generators)
  rw [BinaryMenuCayley8T20.certificate.mem_closure_iff]
  decide +kernel

def inclusionWord : FiniteGeneratorWord (Fin 3) := (.mul (.mul (.inv (.generator 0)) (.mul (.generator 1) (.generator 2))) (.mul (.generator 0) (.mul (.inv (.generator 2)) (.generator 0))))

theorem inclusion_equation : inclusionWord.eval sourceGenerators = extensionElement := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem element_mem_adjoin : extensionElement ∈
    (H ⊔ Subgroup.closure {representatives (S8Seed20NormalizerRoots.roots 30)} : Subgroup Ambient) := by
  rw [← inclusion_equation]
  have h := inclusionWord.eval_mem_closure sourceGenerators
  simpa only [sourceGenerators, Matrix.range_cons, Subgroup.closure_union, sup_comm] using h

abbrev extendedSeed : Subgroup Ambient := H ⊔ Subgroup.zpowers extensionElement

theorem extended_isPGroup : IsPGroup 2 extendedSeed :=
  extension_isPGroup H (IsPGroup.of_card (n := 5) BinaryMenuCayley8T20.exact_card)
    extensionElement 3 power_eq_one normalizes_seed

theorem extended_card_gt : 32 < Nat.card extendedSeed := by
  have h := card_lt_extension H extensionElement outside_seed
  change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T20.generators)) < _ at h
  rw [BinaryMenuCayley8T20.exact_card] at h
  exact h

theorem extended_le_adjoin : extendedSeed ≤
    H ⊔ Subgroup.closure {representatives (S8Seed20NormalizerRoots.roots 30)} :=
  extension_le H _ le_sup_left extensionElement element_mem_adjoin

end SymmetricSubgroupAsymptotics.S8Seed20Root30BinaryExtension
end
