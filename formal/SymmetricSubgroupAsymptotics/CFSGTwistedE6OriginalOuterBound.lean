import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckTorusStabilizer
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalPairAlignment
import SymmetricSubgroupAsymptotics.CFSGOuterAlignedIndex

/-! Actual original twisted E6 outer automorphisms are bounded by the
compatible Cartan scalar index and one extension-field automorphism.
All original automorphisms are aligned only by inner automorphisms. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6OriginalOuterBound
open CFSGTwistedE6GeckTorusStabilizer CFSGTwistedE6GeckStabilizerParameters
open CFSGTwistedE6GeckOriginalProjection CFSGTwistedE6GeckOriginalPairAlignment
open CFSGOuterAlignedIndex PrimitiveSocleRawStructure

theorem typeTwistedE6_outer_card_le (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    Nat.card (Outer (CFSG.Models.TwistedE6 q))≤3*Nat.card (RingAut (q.Extension 2)) := by
  letI := original_finite q
  have hbound := outer_card_le_aligned_index (pairStabilizer q) (productTorusPairHom q).range
    (fun f => by
      obtain ⟨g,hU,hV⟩ := original_exists_inner_fix_pair q f
      refine ⟨g,?_⟩
      intro neg
      cases neg
      · exact hU
      · exact hV)
    (product_torus_inner q)
  exact hbound.trans (product_torus_index_le q)

end SymmetricSubgroupAsymptotics.CFSGTwistedE6OriginalOuterBound
