import SymmetricSubgroupAsymptotics.S8Seed5NormalizerRoots
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop11CatalogueBinding
import Mathlib.Tactic.FinCases

/-! One literal low-root point chart certified by ordinary words in both
directions. No row order or finite-action classification enters the proof. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed5LowRoot161Canonical
open S8Seed5LeftCosets

def sourceGenerators : Fin 3 → Ambient :=
  Matrix.vecCons (representatives (S8Seed5NormalizerRoots.roots 161)) BinaryMenuCayley8T5.generators

theorem source_closure : Subgroup.closure (Set.range sourceGenerators) =
    H ⊔ Subgroup.closure {representatives (S8Seed5NormalizerRoots.roots 161)} := by
  simp only [sourceGenerators,Matrix.range_cons,Subgroup.closure_union,sup_comm]

def conjugator : Ambient where
  toFun := ![0, 1, 4, 7, 6, 3, 2, 5]
  invFun := ![0, 1, 6, 5, 2, 7, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    sourceGenerators PrimitiveAffineEightTop11CatalogueBinding.catalogueGenerators where
  forward := {
    words := ![(.mul (.inv (.generator 1)) (.inv (.generator 0))), (.mul (.generator 1) (.mul (.generator 0) (.inv (.generator 1)))), (.generator 0)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.generator 2), (.mul (.inv (.generator 2)) (.inv (.generator 0)))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem canonical_conjugated : MulAut.conj conjugator •
    (H ⊔ Subgroup.closure {representatives (S8Seed5NormalizerRoots.roots 161)}) =
      PrimitiveAffineEightTop11CatalogueBinding.catalogueAction := by
  change (H ⊔ Subgroup.closure {representatives (S8Seed5NormalizerRoots.roots 161)}).map
    (MulAut.conj conjugator).toMonoidHom = _
  rw [←source_closure]
  exact certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.S8Seed5LowRoot161Canonical
end
