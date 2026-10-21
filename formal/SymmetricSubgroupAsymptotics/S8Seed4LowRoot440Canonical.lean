import SymmetricSubgroupAsymptotics.S8Seed4NormalizerRoots
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop2CatalogueBinding
import Mathlib.Tactic.FinCases

/-! One literal low-root point chart certified by ordinary words in both
directions. No row order or finite-action classification enters the proof. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed4LowRoot440Canonical
open S8Seed4LeftCosets

def sourceGenerators : Fin 3 → Ambient :=
  Matrix.vecCons (representatives (S8Seed4NormalizerRoots.roots 440)) BinaryMenuCayley8T4.generators

theorem source_closure : Subgroup.closure (Set.range sourceGenerators) =
    H ⊔ Subgroup.closure {representatives (S8Seed4NormalizerRoots.roots 440)} := by
  simp only [sourceGenerators,Matrix.range_cons,Subgroup.closure_union,sup_comm]

def conjugator : Ambient where
  toFun := ![0, 3, 1, 7, 5, 2, 4, 6]
  invFun := ![0, 2, 5, 1, 6, 4, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    sourceGenerators PrimitiveAffineEightTop2CatalogueBinding.catalogueGenerators where
  forward := {
    words := ![(.mul (.generator 0) (.mul (.generator 2) (.generator 0))), (.mul (.generator 1) (.generator 2)), (.generator 0)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.generator 2), (.mul (.generator 2) (.mul (.generator 1) (.generator 0))), (.mul (.generator 2) (.mul (.generator 0) (.generator 2)))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem canonical_conjugated : MulAut.conj conjugator •
    (H ⊔ Subgroup.closure {representatives (S8Seed4NormalizerRoots.roots 440)}) =
      PrimitiveAffineEightTop2CatalogueBinding.catalogueAction := by
  change (H ⊔ Subgroup.closure {representatives (S8Seed4NormalizerRoots.roots 440)}).map
    (MulAut.conj conjugator).toMonoidHom = _
  rw [←source_closure]
  exact certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.S8Seed4LowRoot440Canonical
end
