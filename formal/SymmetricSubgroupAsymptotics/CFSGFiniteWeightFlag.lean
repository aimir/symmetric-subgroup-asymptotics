import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Order.Basic
import Mathlib.Algebra.Order.Group.Int
import Lean.Elab.Tactic.Omega

/-! Every finite integer grading admits a literal complete coordinate
flag, with all higher-weight vectors placed first. Equal weights are
ordered by a fixed coordinate tiebreaker, not assumed distinct. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFiniteWeightFlag
variable {I : Type*} [Fintype I]

theorem exists_flag (weight : I→ℤ) : ∃ e : I≃Fin (Fintype.card I),
    ∀ i j,weight j<weight i→e i<e j := by
  let key : I→ℤ ×ₗ Fin (Fintype.card I) := fun i=>(-weight i,Fintype.equivFin I i)
  have hinj : Function.Injective key := by
    intro i j he
    apply (Fintype.equivFin I).injective
    exact congrArg Prod.snd he
  letI : LinearOrder I := LinearOrder.lift' key hinj
  let e : I ≃o Fin (Fintype.card I) := (Fintype.orderIsoFinOfCardEq I rfl).symm
  refine ⟨e.toEquiv,?_⟩
  intro i j hij
  apply e.strictMono
  change key i<key j
  exact Prod.Lex.left _ _ (by omega)

end SymmetricSubgroupAsymptotics.CFSGFiniteWeightFlag
