import SymmetricSubgroupAsymptotics.CFSGFFourE6TorusStabilizer
import SymmetricSubgroupAsymptotics.CFSGFFourE6SimpleStabilizerIndex
import SymmetricSubgroupAsymptotics.CFSGOuterAlignedIndex
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsParameters

/-! Actual original F4 automorphisms are aligned by inner automorphisms
on the opposite Sylow pair. The signed simple-label permutation has
index at most two, including possible path reversal in characteristic
two. The label kernel modulo actual inner product tori has index at
most the actual field-automorphism count. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalOuterBound
open CFSGFFourE6TorusStabilizer CFSGFFourE6OriginalSimpleStabilizer
open CFSGFFourE6SimpleStabilizerIndex CFSGFFourE6OriginalPairAlignment
open CFSGFFourE6OriginalProjection CFSGOuterAlignedIndex PrimitiveSocleRawStructure
open CFSG.Models.Chevalley

theorem original_outer_card_le (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    Nat.card (Outer (Projective CartanMatrix.F₄ K))≤2*Nat.card (RingAut K) := by
  letI := original_finite K
  have hbound := outer_card_le_aligned_tower (pairStabilizer K p) (simpleStabilizer K p)
    (productTorusSimpleHom K p).range
    (fun f => by
      obtain ⟨g,hU,hV⟩ := original_exists_inner_fix_pair K p f
      refine ⟨g,?_⟩
      intro neg
      cases neg
      · exact hU
      · exact hV)
    (product_torus_inner K p) 2 (Nat.card (RingAut K))
    (simple_stabilizer_index_le_two K p) (product_torus_index_le K p)
  exact hbound.trans_eq (Nat.mul_comm _ _)

theorem typeFFour_outer_card_le_two_exponent (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.F4 q)] :
    Nat.card (Outer (CFSG.Models.F4 q))≤2*q.exponent := by
  simpa only [CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q] using
    original_outer_card_le q.Field q.prime

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalOuterBound
