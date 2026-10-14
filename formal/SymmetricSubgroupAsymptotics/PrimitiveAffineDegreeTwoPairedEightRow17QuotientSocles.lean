import SymmetricSubgroupAsymptotics.FiniteNormalJoinTwoGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop17NormalCertificate

/-!
# Quotient socles for paired-eight row 17

Every one of the 11 checked normal states is reached from bottom by two
class-representative transitions. Their existing word certificates give
two ambient normal generators. Mapping generators of the preimage of each
quotient socle proves the uniform two-generator bound.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPairedEightRow17QuotientSocles

abbrev Source := PrimitiveAffineEightFrameTop17TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop17TopCertificate.group

abbrev Top := Subgroup.closure
  (Set.range PrimitiveAffineEightFrameTop17TopCertificate.generators)

/-- Only the finite state transition indices are reduced here. -/
private theorem two_steps (i : Fin 11) :
    ∃ a b : Fin 20,
      PrimitiveAffineEightFrameTop17NormalCertificate.child
        (PrimitiveAffineEightFrameTop17NormalCertificate.child 0 a) b = i := by
  fin_cases i
  · exact ⟨0, 0, rfl⟩
  · exact ⟨0, 16, rfl⟩
  · exact ⟨0, 4, rfl⟩
  · exact ⟨0, 1, rfl⟩
  · exact ⟨0, 8, rfl⟩
  · exact ⟨0, 12, rfl⟩
  · exact ⟨0, 9, rfl⟩
  · exact ⟨0, 13, rfl⟩
  · exact ⟨0, 2, rfl⟩
  · exact ⟨0, 5, rfl⟩
  · exact ⟨1, 2, rfl⟩

theorem source_normal_generators (N : Subgroup Source) (hN : N.Normal) :
    ∃ x : Fin 2 → Source, Subgroup.normalClosure (Set.range x) = N := by
  letI := hN
  exact PrimitiveAffineEightFrameTop17NormalCertificate.data.toRegistry.normal_generating_pair
    two_steps N

theorem top_normal_generators (N : Subgroup Top) (hN : N.Normal) :
    ∃ x : Fin 2 → Top, Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective
    PrimitiveAffineEightFrameTop17TopCertificate.originalEquiv.toMonoidHom
    PrimitiveAffineEightFrameTop17TopCertificate.originalEquiv.surjective
    source_normal_generators N hN

theorem topSocle (N : {N : Subgroup Top // N.Normal}) :
    SocleNormalGeneratorBound (Top ⧸ N.1) 2 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    top_normal_generators N.1

end PrimitiveAffineDegreeTwoPairedEightRow17QuotientSocles
end SymmetricSubgroupAsymptotics

end
