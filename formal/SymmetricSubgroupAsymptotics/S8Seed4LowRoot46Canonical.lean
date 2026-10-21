import SymmetricSubgroupAsymptotics.S8Seed4NormalizerRoots
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop21CatalogueBinding
import Mathlib.Tactic.FinCases

/-! One literal low-root point chart certified by ordinary words in both
directions. No row order or finite-action classification enters the proof. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed4LowRoot46Canonical
open S8Seed4LeftCosets

def sourceGenerators : Fin 3 → Ambient :=
  Matrix.vecCons (representatives (S8Seed4NormalizerRoots.roots 46)) BinaryMenuCayley8T4.generators

theorem source_closure : Subgroup.closure (Set.range sourceGenerators) =
    H ⊔ Subgroup.closure {representatives (S8Seed4NormalizerRoots.roots 46)} := by
  simp only [sourceGenerators,Matrix.range_cons,Subgroup.closure_union,sup_comm]

def conjugator : Ambient where
  toFun := ![0, 1, 2, 5, 4, 7, 3, 6]
  invFun := ![0, 1, 2, 6, 4, 3, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    sourceGenerators PrimitiveAffineEightTop21CatalogueBinding.catalogueGenerators where
  forward := {
    words := ![(.mul (.mul (.generator 1) (.generator 0)) (.mul (.generator 0) (.generator 2))), (.mul (.mul (.generator 0) (.generator 2)) (.mul (.generator 0) (.mul (.generator 0) (.inv (.generator 1))))), (.mul (.mul (.generator 0) (.generator 2)) (.mul (.generator 0) (.mul (.generator 0) (.generator 2))))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.generator 0) (.mul (.inv (.generator 1)) (.generator 0))), (.mul (.mul (.generator 1) (.inv (.generator 0))) (.mul (.inv (.generator 1)) (.mul (.generator 0) (.generator 1)))), (.mul (.mul (.generator 1) (.generator 0)) (.mul (.generator 1) (.mul (.generator 1) (.generator 0))))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem canonical_conjugated : MulAut.conj conjugator •
    (H ⊔ Subgroup.closure {representatives (S8Seed4NormalizerRoots.roots 46)}) =
      PrimitiveAffineEightTop21CatalogueBinding.catalogueAction := by
  change (H ⊔ Subgroup.closure {representatives (S8Seed4NormalizerRoots.roots 46)}).map
    (MulAut.conj conjugator).toMonoidHom = _
  rw [←source_closure]
  exact certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.S8Seed4LowRoot46Canonical
end
