import SymmetricSubgroupAsymptotics.CFSGQuadraticRootOrdinaryGenerators
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalProjection

/-! Prime-field ordinary generators of the literal original simply-laced
projective Serre model. The finite parameter set is mapped through the
checked ACTUAL surjective originalProjection. No source faithfulness,
unspecified isomorphism, global permutation input, or two-generation
theorem is assumed. Simplicity is required only by the existing original
projection construction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoOriginalOrdinaryGenerators
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoCoordinateOriginalProjection

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Finite K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem exists_generating_finset
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (p : ℕ) [Fact p.Prime] [Module (ZMod p) K] [Module.Finite (ZMod p) K] :
    ∃ S : Finset (Projective (cartan b₀ s₀) K),
      Subgroup.closure (S : Set (Projective (cartan b₀ s₀) K)) = ⊤ ∧
        S.card ≤ (2*r)*Module.finrank (ZMod p) K := by
  obtain ⟨S,hS,hcard⟩ := CFSGQuadraticRootOrdinaryGenerators.exists_generating_finset
    (realizationData A hs hp b₀ s₀) K p
  let π := originalProjection A hd hs hp ho K i
  have hπ := originalProjection_surjective A hd hs hp ho K i
  refine ⟨S.image π,?_,Finset.card_image_le.trans hcard⟩
  rw [Finset.coe_image,← MonoidHom.map_closure,hS]
  exact Subgroup.map_top_of_surjective π hπ

theorem genRank_le_twice_rank_mul_finrank
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (p : ℕ) [Fact p.Prime] [Module (ZMod p) K] [Module.Finite (ZMod p) K] :
    MarkedC4.genRank (Projective (cartan b₀ s₀) K) ≤
      (2*r)*Module.finrank (ZMod p) K := by
  obtain ⟨S,hS,hcard⟩ := exists_generating_finset A hd hs hp ho K i p
  exact (MarkedC4.genRank_le hS).trans hcard

end SymmetricSubgroupAsymptotics.CFSGNormTwoOriginalOrdinaryGenerators
