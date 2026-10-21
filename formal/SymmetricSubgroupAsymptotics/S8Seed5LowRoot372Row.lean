import SymmetricSubgroupAsymptotics.S8Seed5LowModels

/-! One actual low-row equality certified by ordinary words in both
directions. No cardinality or catalogue correspondence is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed5LowRoot372Row
open S8Seed5LeftCosets S8Seed5LowModels

def sourceGenerators : Fin 3 → Ambient :=
  Matrix.vecCons (representatives (S8Seed5NormalizerRoots.roots 372)) BinaryMenuCayley8T5.generators

theorem source_closure : Subgroup.closure (Set.range sourceGenerators) =
    H ⊔ Subgroup.closure {representatives (S8Seed5NormalizerRoots.roots 372)} := by
  simp only [sourceGenerators, Matrix.range_cons, Subgroup.closure_union, sup_comm]

def certificate : FiniteGeneratorEquivWordCertificate (MulEquiv.refl Ambient)
    sourceGenerators (generators 3) where
  forward := {
    words := ![(.generator 0), (.generator 1), (.generator 2)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.generator 0), (.generator 1), (.generator 2)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem root_row : H ⊔ Subgroup.closure {representatives (S8Seed5NormalizerRoots.roots 372)} = rows 3 := by
  have h := certificate.map_closure_eq
  change (Subgroup.closure (Set.range sourceGenerators)).map (MonoidHom.id Ambient) = rows 3 at h
  rw [Subgroup.map_id, source_closure] at h
  exact h

end SymmetricSubgroupAsymptotics.S8Seed5LowRoot372Row
end
