import SymmetricSubgroupAsymptotics.PermutationOrbitHeadSection

/-! Restriction of invariant forms to an actual subgroup is injective.
The underlying permutation submodule is retained, not replaced by an
invariant section of a different representation. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {k G X : Type} [Field k] [Group G] [MulAction G X]

/-- The same original function subspace, acted on by the actual subgroup. -/
def permutationSubrepresentationRestrict (N : Subgroup G)
    (M : Subrepresentation (permutationFunctionRepresentation k G X)) :
    Subrepresentation (permutationFunctionRepresentation k N X) where
  toSubmodule := M.toSubmodule
  apply_mem_toSubmodule n v hv := M.apply_mem_toSubmodule n.val hv

/-- Restrict an invariant linear form without changing its underlying map. -/
def permutationHeadRestrict (N : Subgroup G)
    (M : Subrepresentation (permutationFunctionRepresentation k G X)) :
    (M.toRepresentation.IntertwiningMap (Representation.trivial k G k)) →ₗ[k]
      ((permutationSubrepresentationRestrict N M).toRepresentation.IntertwiningMap
        (Representation.trivial k N k)) where
  toFun f := {
    toLinearMap := f.toLinearMap
    isIntertwining' n := f.isIntertwining' n.val }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem permutationHeadRestrict_injective (N : Subgroup G)
    (M : Subrepresentation (permutationFunctionRepresentation k G X)) :
    Function.Injective (permutationHeadRestrict N M) := by
  intro f g h
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  exact congrArg (fun z => z v) h

theorem permutationHead_finrank_le_subgroup [Finite X]
    (N : Subgroup G)
    (M : Subrepresentation (permutationFunctionRepresentation k G X)) :
    Module.finrank k (M.toRepresentation.IntertwiningMap
      (Representation.trivial k G k)) ≤
    Module.finrank k
      ((permutationSubrepresentationRestrict N M).toRepresentation.IntertwiningMap
        (Representation.trivial k N k)) :=
  (permutationHeadRestrict N M).finrank_le_finrank_of_injective
    (permutationHeadRestrict_injective N M)

end SymmetricSubgroupAsymptotics
