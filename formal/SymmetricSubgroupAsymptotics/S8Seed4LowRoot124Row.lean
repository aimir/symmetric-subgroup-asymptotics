import SymmetricSubgroupAsymptotics.S8Seed4LowModels

/-! One actual low-row equality certified by ordinary words in both
directions. No cardinality or catalogue correspondence is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed4LowRoot124Row
open S8Seed4LeftCosets S8Seed4LowModels

def sourceGenerators : Fin 3 → Ambient :=
  Matrix.vecCons (representatives (S8Seed4NormalizerRoots.roots 124)) BinaryMenuCayley8T4.generators

theorem source_closure : Subgroup.closure (Set.range sourceGenerators) =
    H ⊔ Subgroup.closure {representatives (S8Seed4NormalizerRoots.roots 124)} := by
  simp only [sourceGenerators, Matrix.range_cons, Subgroup.closure_union, sup_comm]

def certificate : FiniteGeneratorEquivWordCertificate (MulEquiv.refl Ambient)
    sourceGenerators (generators 1) where
  forward := {
    words := ![(.mul (.mul (.generator 0) (.generator 1)) (.mul (.generator 1) (.mul (.generator 0) (.generator 1)))), (.generator 1), (.generator 2)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.mul (.generator 0) (.mul (.generator 2) (.generator 1))) (.mul (.generator 0) (.mul (.generator 1) (.generator 0)))), (.generator 1), (.generator 2)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem root_row : H ⊔ Subgroup.closure {representatives (S8Seed4NormalizerRoots.roots 124)} = rows 1 := by
  have h := certificate.map_closure_eq
  change (Subgroup.closure (Set.range sourceGenerators)).map (MonoidHom.id Ambient) = rows 1 at h
  rw [Subgroup.map_id, source_closure] at h
  exact h

end SymmetricSubgroupAsymptotics.S8Seed4LowRoot124Row
end
