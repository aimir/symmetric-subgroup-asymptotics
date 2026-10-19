import SymmetricSubgroupAsymptotics.PermutationalWreathTransport
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! A subgroup conjugacy supplies the exact equivariant chart needed for
wreath transport, including the actual group map on the top. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.PermutationConjugateTopChart
variable {I : Type} (B D : Subgroup (Equiv.Perm I)) (g : Equiv.Perm I)
  (h : MulAut.conj g • B=D)

def groupChart : B ≃* D :=
  (Subgroup.equivSMul (MulAut.conj g) B).trans (MulEquiv.subgroupCongr h)

include h in
theorem equivariant (b : B) (i : I) :
    g (b • i) = groupChart B D g h b • g i := by
  change g ((b : Equiv.Perm I) i) =
    (g * (b : Equiv.Perm I) * g⁻¹) (g i)
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply]

/-- Transport every actual correlated subgroup using the conjugating points. -/
def wreathChart {A : Type} [Group A] :
    PermutationalWreathProduct A B I ≃* PermutationalWreathProduct A D I :=
  PermutationalWreathProduct.transport (groupChart B D g h) g
    (equivariant B D g h)
end SymmetricSubgroupAsymptotics.PermutationConjugateTopChart
