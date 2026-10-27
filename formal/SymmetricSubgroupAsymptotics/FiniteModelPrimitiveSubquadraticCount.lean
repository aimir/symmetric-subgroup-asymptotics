import SymmetricSubgroupAsymptotics.FiniteModelPrimitiveLabelledCount
import SymmetricSubgroupAsymptotics.FactorialLogSquaredSubquadraticCount

/-! Complete weak subquadratic count for every fixed finite family of actual
nonaffine primitive simple models, including arbitrarily many socle factors.
This is not the count of all transitive imprimitive groups. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FiniteModelPrimitiveSubquadraticCount
open FiniteModelPrimitiveLabelledCount

variable {ι : Type} [Finite ι] (M : ι → Type) [∀ i,Group (M i)]

local instance (n : ℕ) : Fintype (Sector M n) := Fintype.ofFinite _

theorem sector_subquadratic : SubquadraticMenuIndexCount (Sector M) := by
  obtain ⟨C,hC⟩ := exists_uniform_count_budget M
  exact FactorialLogSquaredSubquadraticCount.subquadratic_of_factorial_budget C hC

end SymmetricSubgroupAsymptotics.FiniteModelPrimitiveSubquadraticCount
