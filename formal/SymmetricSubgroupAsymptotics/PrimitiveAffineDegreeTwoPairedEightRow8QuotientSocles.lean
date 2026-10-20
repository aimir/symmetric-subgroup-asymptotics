import SymmetricSubgroupAsymptotics.FiniteNormalJoinTwoGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop8NormalCertificate

/-!
# Quotient socles for paired-eight row 8

Every one of the 11 checked normal states is reached from bottom by two
class-representative transitions. Their existing word certificates give
two ambient normal generators. Mapping generators of the preimage of each
quotient socle proves the uniform two-generator bound.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPairedEightRow8QuotientSocles

abbrev Source := PrimitiveAffineEightFrameTop8TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop8TopCertificate.group

abbrev Top := Subgroup.closure
  (Set.range PrimitiveAffineEightFrameTop8TopCertificate.generators)

/-- Only the finite state transition indices are reduced here. -/
private theorem two_steps (i : Fin 11) :
    ∃ a b : Fin 16,
      PrimitiveAffineEightFrameTop8NormalCertificate.child
        (PrimitiveAffineEightFrameTop8NormalCertificate.child 0 a) b = i := by
  fin_cases i
  · exact ⟨0, 0, rfl⟩
  · exact ⟨0, 3, rfl⟩
  · exact ⟨0, 7, rfl⟩
  · exact ⟨0, 15, rfl⟩
  · exact ⟨0, 6, rfl⟩
  · exact ⟨0, 4, rfl⟩
  · exact ⟨0, 2, rfl⟩
  · exact ⟨0, 1, rfl⟩
  · exact ⟨0, 9, rfl⟩
  · exact ⟨0, 12, rfl⟩
  · exact ⟨1, 4, rfl⟩

theorem source_normal_generators (N : Subgroup Source) (hN : N.Normal) :
    ∃ x : Fin 2 → Source, Subgroup.normalClosure (Set.range x) = N := by
  letI := hN
  exact PrimitiveAffineEightFrameTop8NormalCertificate.data.toRegistry.normal_generating_pair
    two_steps N

theorem top_normal_generators (N : Subgroup Top) (hN : N.Normal) :
    ∃ x : Fin 2 → Top, Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective
    PrimitiveAffineEightFrameTop8TopCertificate.originalEquiv.toMonoidHom
    PrimitiveAffineEightFrameTop8TopCertificate.originalEquiv.surjective
    source_normal_generators N hN

theorem topSocle (N : {N : Subgroup Top // N.Normal}) :
    SocleNormalGeneratorBound (Top ⧸ N.1) 2 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    top_normal_generators N.1

end PrimitiveAffineDegreeTwoPairedEightRow8QuotientSocles
end SymmetricSubgroupAsymptotics

end
