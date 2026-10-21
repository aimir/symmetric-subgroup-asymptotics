import SymmetricSubgroupAsymptotics.BinaryCoordinateSpaces

/-! Restriction of the binary permutation action preserves literal vector
coordinates. The proof is generic in BOTH ambient permutation subgroups,
so no closed finite-group implementation is normalized here. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem binaryPermutation_subgroup_restriction {w : ℕ}
    (A B : Subgroup (Equiv.Perm (Fin w))) (h : A ≤ B)
    (t : A) (v : Fin w → ZMod 2) :
    ((binaryPermutationRepresentation w).comp B.subtype) (Subgroup.inclusion h t) v =
      ((binaryPermutationRepresentation w).comp A.subtype) t v := by
  change binaryPermutationRepresentation w
      ((Subgroup.inclusion h t : B) : Equiv.Perm (Fin w)) v =
    binaryPermutationRepresentation w (t : Equiv.Perm (Fin w)) v
  exact congrArg (fun p : Equiv.Perm (Fin w) => binaryPermutationRepresentation w p v)
    (Subgroup.coe_inclusion h t)
end SymmetricSubgroupAsymptotics
