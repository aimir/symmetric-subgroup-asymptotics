import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.StdBasis

/-!
# Self-duality of finite permutation-function representations

The coordinate pairing on `X → k` is invariant under permutation.  We
package that elementary fact as an equivalence with the contragredient, then
use it to turn finite cyclic-generator certificates for the natural module
into the dual uniform bound required by the Schur-capacity argument.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable {k G X : Type*} [Field k] [Group G] [MulAction G X] [Finite X]

/-- The standard-coordinate pairing identifies a finite permutation module
with its contragredient. -/
noncomputable def permutationFunctionRepresentationSelfDual :
    (permutationFunctionRepresentation k G X).Equiv
      (permutationFunctionRepresentation k G X).dual :=
  Representation.Equiv.mk (Pi.basisFun k X).toDualEquiv (fun g ↦ by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext_on (Pi.basisFun k X).span_eq
    rintro _ ⟨x, rfl⟩
    have hbasis :
        permutationFunctionRepresentation k G X g⁻¹
            (Pi.basisFun k X x) =
          Pi.basisFun k X (g⁻¹ • x) := by
      funext y
      simp only [permutationFunctionRepresentation_apply,
        Pi.basisFun_apply, Pi.single_apply]
      by_cases h : g • y = x
      · have hy : y = g⁻¹ • x := by
          simpa only [inv_smul_smul] using congrArg (fun z ↦ g⁻¹ • z) h
        simp [h, hy]
      · have hy : y ≠ g⁻¹ • x := by
          intro hy
          apply h
          simpa only [hy, smul_inv_smul]
        simp [h, hy]
    change (Pi.basisFun k X).toDualEquiv
          (permutationFunctionRepresentation k G X g f)
          (Pi.basisFun k X x) =
      (Pi.basisFun k X).toDualEquiv f
        (permutationFunctionRepresentation k G X g⁻¹
          (Pi.basisFun k X x))
    rw [hbasis]
    simp only [Basis.toDualEquiv_apply, Basis.toDual_apply_left,
      Pi.basisFun_repr, permutationFunctionRepresentation_apply])

/-- A uniform generator bound for the natural permutation module also holds
for its dual, with the same padded tuple length. -/
theorem permutationFunctionRepresentation_dual_uniform
    {H : ℕ}
    (h : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation k G X) H) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation k G X).dual H :=
  h.of_surjective
    permutationFunctionRepresentationSelfDual.toIntertwiningMap
    permutationFunctionRepresentationSelfDual.surjective

end SymmetricSubgroupAsymptotics

end
