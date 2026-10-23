import SymmetricSubgroupAsymptotics.CFSGTwistedDNormalizeFirstPair
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedQuadraticPairTail

/-! Recursive frame elimination by literal relative-root words leaves
an actual isometry of the final two-dimensional plane. Its defining
fixedness is retained as the literal rank-two extension condition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFrameReduction
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDIndexQuadraticForm CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDNaturalFieldTwist CFSGSerreOrdinaryTwists
open CFSGTwistedDRelativeTailEmbedding

def residualEmbedding (K : Type) [Field K] :
    (n : ℕ) → ((Mat K 1)ˣ →* (Mat K (n + 2))ˣ)
  | 0 => tailUnitHom K 1
  | n + 1 => (tailUnitHom K (n + 2)).comp (residualEmbedding K n)

theorem residualEmbedding_zero (K : Type) [Field K] (b : (Mat K 1)ˣ) :
    residualEmbedding K 0 b = tailUnitHom K 1 b := rfl

theorem residualEmbedding_succ (K : Type) [Field K] (n : ℕ) (b : (Mat K 1)ˣ) :
    residualEmbedding K (n + 1) b = tailUnitHom K (n + 2) (residualEmbedding K n b) := rfl

theorem relative_mul_properties (n : ℕ) (q : CFSG.PrimePower)
    (u : (Mat (q.Extension 2) (n + 2))ˣ)
    (hQ : u ∈ quadraticPreserving (q.Extension 2) (n + 2))
    (ht : unitTwist (q.Extension 2) n (definingFieldAutomorphism q 2) u = u)
    (a : relativeRootGroup n q) :
    a.val * u ∈ quadraticPreserving (q.Extension 2) (n + 2) ∧
      unitTwist (q.Extension 2) n (definingFieldAutomorphism q 2) (a.val * u) = a.val * u := by
  have haQ : a.val ∈ quadraticPreserving (q.Extension 2) (n + 2) :=
    CFSGOrthogonalDAllRankQuadraticPreservation.elementary_le_quadratic (q.Extension 2) n
      (relativeRootGroup_le_elementary n q a.property)
  have hat : unitTwist (q.Extension 2) n (definingFieldAutomorphism q 2) a.val = a.val :=
    CFSGTwistedDRelativeFixedGroup.relativeRootGroup_le_fixed n q a.property
  refine ⟨(quadraticPreserving (q.Extension 2) (n + 2)).mul_mem haQ hQ, ?_⟩
  rw [map_mul, hat, ht]

theorem exists_residual (n : ℕ) (q : CFSG.PrimePower)
    (u : (Mat (q.Extension 2) (n + 2))ˣ)
    (hQ : u ∈ quadraticPreserving (q.Extension 2) (n + 2))
    (ht : unitTwist (q.Extension 2) n (definingFieldAutomorphism q 2) u = u) :
    ∃ a : relativeRootGroup n q, ∃ b : quadraticPreserving (q.Extension 2) 1,
      a.val * u = residualEmbedding (q.Extension 2) n b.val ∧
      unitTwist (q.Extension 2) 0 (definingFieldAutomorphism q 2)
        (tailUnitHom (q.Extension 2) 1 b.val) = tailUnitHom (q.Extension 2) 1 b.val := by
  induction n with
  | zero =>
    obtain ⟨a, hp, hn⟩ := CFSGTwistedDNormalizeFirstPair.exists_normalize_first_pair 0 q u hQ ht
    obtain ⟨hvQ, hvt⟩ := relative_mul_properties 0 q u hQ ht a
    obtain ⟨b, hb⟩ := CFSGOrthogonalDQuadraticPairTail.exists_quadratic_tail
      (q.Extension 2) 1 (a.val * u) hvQ hp hn
    refine ⟨a, b, hb.symm, ?_⟩
    rw [hb]
    exact hvt
  | succ n ih =>
    obtain ⟨a, hp, hn⟩ := CFSGTwistedDNormalizeFirstPair.exists_normalize_first_pair (n + 1) q u hQ ht
    obtain ⟨hvQ, hvt⟩ := relative_mul_properties (n + 1) q u hQ ht a
    obtain ⟨v, hv, hvfixed⟩ := CFSGTwistedDFixedQuadraticPairTail.exists_fixed_quadratic_tail
      (q.Extension 2) n (definingFieldAutomorphism q 2) (a.val * u) hvQ hvt hp hn
    obtain ⟨b, c, hbc, hc⟩ := ih v.val v.property hvfixed
    let d : relativeRootGroup (n + 1) q := tailRelativeHom n q b * a
    refine ⟨d, c, ?_, hc⟩
    change (tailUnitHom (q.Extension 2) (n + 2) b.val * a.val) * u = _
    rw [mul_assoc, ← hv, ← map_mul, hbc]
    rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedDFrameReduction
