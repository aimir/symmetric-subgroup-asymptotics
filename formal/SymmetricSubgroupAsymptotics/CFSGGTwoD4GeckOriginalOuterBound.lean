import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckTorusStabilizer
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalPairAlignment
import SymmetricSubgroupAsymptotics.CFSGOuterAlignedIndex
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsParameters

/-! The original G2 Out count uses actual inner opposed-pair alignment,
the at-most-two signed-label permutation, and the actual inner scalar
range of index at most the common field-automorphism count. No
root-length-preservation assertion is made in characteristic three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalOuterBound
open CFSGGTwoD4GeckTorusStabilizer CFSGGTwoD4GeckOriginalSimpleStabilizer
open CFSGGTwoD4GeckOriginalPairAlignment CFSGGTwoD4GeckOriginalProjection
open CFSGOuterAlignedIndex PrimitiveSocleRawStructure CFSG.Models.Chevalley

theorem original_outer_card_le (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    Nat.card (Outer (Projective CartanMatrix.G₂ K))≤2*Nat.card (RingAut K) := by
  letI := original_finite K
  have hb := outer_card_le_aligned_tower (pairStabilizer K p) (simpleStabilizer K p)
    (productTorusSimpleHom K p).range (fun f=>by
      obtain ⟨g,hU,hV⟩ := original_exists_inner_fix_pair K p f
      refine ⟨g,?_⟩
      intro neg
      cases neg
      · exact hU
      · exact hV)
    (product_torus_inner K p) 2 (Nat.card (RingAut K))
    (simple_stabilizer_index_le_two K p) (product_torus_index_le K p)
  exact hb.trans_eq (Nat.mul_comm _ _)

theorem typeGTwo_outer_card_le_two_exponent (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.G2 q)] :
    Nat.card (Outer (CFSG.Models.G2 q))≤2*q.exponent := by
  simpa only [CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q] using
    original_outer_card_le q.Field q.prime

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalOuterBound
