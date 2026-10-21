import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerHeadDimension
import SymmetricSubgroupAsymptotics.BinaryPairCentralDerivedFlip

/-! Two head-two pair layers cannot be the same original subspace when
the actual flip kernel contains the constant vector: its mixed products
would kill the entire lower head. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics
local instance highLayerDistinctnessPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem binary_head_four_pair_layer_profile
    {G : Type} [Group G] {w : ℕ}
    (rho : Representation (ZMod 2) G (Fin w → ZMod 2))
    (K : Submodule (ZMod 2) (Fin w → ZMod 2)) (hconstant : (1 : Fin w → ZMod 2) ∈ K)
    (S L : Subrepresentation rho)
    (hS : Module.finrank (ZMod 2) S.toRepresentation.Coinvariants ≤ 2)
    (hL : Module.finrank (ZMod 2) L.toRepresentation.Coinvariants ≤ 2)
    (hhead : 4 ≤ Module.finrank (ZMod 2) S.toRepresentation.Coinvariants +
      Module.finrank (ZMod 2) (L.toSubmodule ⧸
        ((binaryCoordinateProductSpan K S.toSubmodule).comap L.toSubmodule.subtype ⊔
          Representation.Coinvariants.ker L.toRepresentation))) :
    2 ≤ Module.finrank (ZMod 2) S.toRepresentation.Coinvariants ∧
    2 ≤ Module.finrank (ZMod 2) L.toRepresentation.Coinvariants ∧
    S.toSubmodule ≠ L.toSubmodule := by
  let D : Submodule (ZMod 2) L.toSubmodule :=
    (binaryCoordinateProductSpan K S.toSubmodule).comap L.toSubmodule.subtype ⊔
      Representation.Coinvariants.ker L.toRepresentation
  change 4 ≤ Module.finrank (ZMod 2) S.toRepresentation.Coinvariants +
    Module.finrank (ZMod 2) (L.toSubmodule ⧸ D) at hhead
  have hrad : Representation.Coinvariants.ker L.toRepresentation ≤ D := le_sup_right
  have hq := LinearMap.finrank_le_finrank_of_surjective (Submodule.factor_surjective hrad)
  change Module.finrank (ZMod 2) (L.toSubmodule ⧸ D) ≤
    Module.finrank (ZMod 2) L.toRepresentation.Coinvariants at hq
  refine ⟨by omega, by omega, ?_⟩
  intro heq
  have hprod : L.toSubmodule ≤ binaryCoordinateProductSpan K S.toSubmodule := by
    intro v hv
    have hs : v ∈ S.toSubmodule := heq.symm ▸ hv
    simpa only [one_mul] using
      binaryCoordinateProductSpan.product_mem K S.toSubmodule 1 hconstant v hs
  have hDtop : D = ⊤ := by
    apply top_unique
    intro v _
    exact (show (binaryCoordinateProductSpan K S.toSubmodule).comap L.toSubmodule.subtype ≤ D
      from le_sup_left) (hprod v.property)
  have hz : Module.finrank (ZMod 2) (L.toSubmodule ⧸ D) = 0 := by
    rw [hDtop]
    exact Module.finrank_zero_of_subsingleton
  omega

namespace BinaryPairFrame
variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (E : BinaryPairFrame U (Fin w)) [MulAction.IsPretransitive U X]

theorem kernelSpace_contains_one_of_positive_finrank (hU : IsPGroup 2 U) (i : Fin w)
    (hdim : 1 ≤ Module.finrank (ZMod 2) E.kernelSpace) :
    (1 : Fin w → ZMod 2) ∈ E.kernelSpace := by
  letI highLayerDistinctness_topTransitive : MulAction.IsPretransitive E.top.range (Fin w) :=
    E.top_pretransitive
  exact pGroup_permutation_subrepresentation_contains_one (E.top_isPGroup hU) i
    E.kernelTopPermutationSubrepresentation (Submodule.one_le_finrank_iff.mp hdim)

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
