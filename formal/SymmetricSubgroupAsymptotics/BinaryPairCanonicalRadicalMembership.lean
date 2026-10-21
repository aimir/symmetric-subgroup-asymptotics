import SymmetricSubgroupAsymptotics.BinaryPairWholeAxisCoordinateRadical
import SymmetricSubgroupAsymptotics.BinaryPairCanonicalPointCoordinates
import SymmetricSubgroupAsymptotics.BinaryPairFrameConjugateTop
import SymmetricSubgroupAsymptotics.BinaryPairFrameKernelTransport

/-! Canonical carry coordinates retain both directions of membership
in the same original kernel's relative radical. Only pair labels change;
the ambient source and every original normal subgroup remain unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

private theorem relativeRadical_congr_of_eq {G : Type} [Group G]
    (p : ℕ) [Fact p.Prime] (A B : Subgroup G) [A.Normal] [B.Normal] (he : A = B) :
    primeRelativeRadical p A = primeRelativeRadical p B := by
  subst B
  rfl

namespace BinaryPairFrame
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))

theorem canonical_bits_mem_radical_iff
    (R : Submodule (ZMod 2) (Fin 16 → ZMod 2))
    (hrad : ((Representation.Coinvariants.ker
      (F.axisNaturalSubrepresentation F.top.ker).toRepresentation).map
        (F.axisNaturalSubrepresentation F.top.ker).toSubmodule.subtype).map
          E.originalCoordinateEquiv.toLinearMap = R)
    (k' : (F.reindex E.canonicalPointLabels).top.ker) :
    binaryEightCanonicalLayerChange ((F.reindex E.canonicalPointLabels).bits k') ∈ R ↔
      (k' : U) ∈ primeRelativeRadical 2 (F.reindex E.canonicalPointLabels).top.ker := by
  let e := E.canonicalPointLabels
  let k : F.top.ker := ⟨k'.val, by
    have hk : k'.val ∈ (F.reindex e).top.ker := k'.property
    exact (congrArg (fun K : Subgroup U => k'.val ∈ K) (F.reindex_top_ker e)).mp hk⟩
  have hk' : F.reindexKernel e k = k' := Subtype.ext rfl
  have hbits : (F.reindex e).bits k' = fun j => F.bits k (e.symm j) := by
    funext j
    rw [← hk', F.reindexKernel_bits]
  have he : binaryEightCanonicalLayerChange ((F.reindex e).bits k') =
      E.originalCoordinateEquiv (F.bits k) := by
    rw [hbits, E.originalCoordinateEquiv_canonicalPointLabels]
  have hrad' := relativeRadical_congr_of_eq 2 (F.reindex e).top.ker F.top.ker (F.reindex_top_ker e)
  rw [he, hrad']
  exact F.bits_mem_coordinate_radical_iff E.originalCoordinateEquiv R hrad k

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
