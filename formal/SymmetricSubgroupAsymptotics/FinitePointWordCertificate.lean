import SymmetricSubgroupAsymptotics.FiniteGeneratorWord
import Mathlib.GroupTheory.GroupAction.Basic

/-! Original words reaching each literal point certify transitivity.
Only the point orbit is needed; no closure of the permutation group or
normal-subgroup registry is part of the certificate. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

structure FinitePointWordCertificate {X ι : Type*}
    (generators : ι → Equiv.Perm X) where
  basePoint : X
  words : X → FiniteGeneratorWord ι
  reaches : ∀ x : X, (words x).eval generators basePoint = x

namespace FinitePointWordCertificate
variable {X ι : Type*} {generators : ι → Equiv.Perm X}
    (C : FinitePointWordCertificate generators)

include C in
/-- Membership and transitivity use the very same original word. -/
theorem pretransitive :
    MulAction.IsPretransitive (Subgroup.closure (Set.range generators)) X := by
  refine ⟨?_⟩
  intro x y
  let u : Subgroup.closure (Set.range generators) :=
    ⟨(C.words x).eval generators, (C.words x).eval_mem_closure generators⟩
  let v : Subgroup.closure (Set.range generators) :=
    ⟨(C.words y).eval generators, (C.words y).eval_mem_closure generators⟩
  have hx : (u : Equiv.Perm X).symm x = C.basePoint := by
    rw [← C.reaches x]
    exact (u : Equiv.Perm X).symm_apply_apply C.basePoint
  refine ⟨v * u⁻¹, ?_⟩
  change (v : Equiv.Perm X) ((u : Equiv.Perm X).symm x) = y
  rw [hx]
  exact C.reaches y

end FinitePointWordCertificate
end SymmetricSubgroupAsymptotics
end
