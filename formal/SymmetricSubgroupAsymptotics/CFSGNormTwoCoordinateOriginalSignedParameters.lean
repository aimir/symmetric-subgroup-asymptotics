import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordPairCollecting

/-! The same original projection supplies parameters for all signed
root groups. Actual Weyl transports of positive A2 commutators push
forward to the original projective model with their integral unit sign. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSignedParameters
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoCoordinateOriginalProjection
open CFSGNormTwoCoordinateOriginalRootDegree CFSGNormTwoCoordinatePositivePairCollecting
open CFSGNormTwoCoordinateElementaryRootParameters CFSGRootParameterAutomorphism
open CFSGFieldScaledRootHom CFSGCommutatorParameterRange
open CFSGNormTwoCoordinateOriginalA2FieldRecognition
open CFSGNormTwoCoordinateOriginalA2PairStabilizer
open CFSGNormTwoCoordinateOriginalAllRootLines CFSGNormTwoCoordinateRootElementRange
open CFSGNormTwoCoordinateRootSubgroup
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

open CFSGNormTwoCoordinateOriginalSimpleParameters CFSGNormTwoCoordinateWordPairCollecting
open CFSGNormTwoGeckWeylWordDegree

def rootParameterHom [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i : Fin r) (k : Roots A) : Multiplicative K →* Projective (cartan b₀ s₀) K :=
  (originalProjection A hd hs hp ho K i).comp (elementarySelectedRootHom A hd hs hp ho K k)

 theorem rootParameterHom_eq_positive
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (k : Roots A) (hk : ∀ j, 0 ≤ k.val j) :
    rootParameterHom A hd hs hp ho K i k = originalSelectedHom A hd hs hp ho K i k hk := rfl

 theorem rootParameterHom_range
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (k : Roots A) :
    (rootParameterHom A hd hs hp ho K i k).range = originalFullRootLine A hd hs hp ho K i k := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨elementarySelectedRootHom A hd hs hp ho K k a, ?_, rfl⟩
    change (elementarySelectedRootHom A hd hs hp ho K k a).val ∈ rootSubgroup A hd hs hp ho K k
    exact (mem_rootSubgroup_iff_selected A hd hs hp ho K k _).mpr ⟨a.toAdd, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    change x.val ∈ rootSubgroup A hd hs hp ho K k at hx
    obtain ⟨a, ha⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K k x.val).mp hx
    refine ⟨Multiplicative.ofAdd a, ?_⟩
    change originalProjection A hd hs hp ho K i (elementarySelectedRootHom A hd hs hp ho K k _) = _
    apply congrArg (originalProjection A hd hs hp ho K i)
    exact Subtype.ext ha

 theorem original_word_pair_commutator_sign
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (w : List (Fin r)) (k l : Roots A)
    (hk : ∀ t, 0 ≤ k.val t) (hl : ∀ t, 0 ≤ l.val t)
    (hpair : integerPairing A k.val l.val = -1) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ a b : K,
      rootParameterHom A hd hs hp ho K i (wordRoot A hs hp b₀ s₀ w k) (Multiplicative.ofAdd a) *
        rootParameterHom A hd hs hp ho K i (wordRoot A hs hp b₀ s₀ w l) (Multiplicative.ofAdd b) *
        (rootParameterHom A hd hs hp ho K i (wordRoot A hs hp b₀ s₀ w k) (Multiplicative.ofAdd a))⁻¹ *
        (rootParameterHom A hd hs hp ho K i (wordRoot A hs hp b₀ s₀ w l) (Multiplicative.ofAdd b))⁻¹ =
      rootParameterHom A hd hs hp ho K i (wordRoot A hs hp b₀ s₀ w (sumRoot A hs k l hpair))
        (Multiplicative.ofAdd ((ε : K) * (a * b))) := by
  obtain ⟨ε, hε, he⟩ := word_pair_commutator_sign A hd hs hp ho w k l hk hl hpair
  refine ⟨ε, hε, ?_⟩
  intro a b
  have hh : elementarySelectedRootHom A hd hs hp ho K (wordRoot A hs hp b₀ s₀ w k)
        (Multiplicative.ofAdd a) *
      elementarySelectedRootHom A hd hs hp ho K (wordRoot A hs hp b₀ s₀ w l)
        (Multiplicative.ofAdd b) *
      (elementarySelectedRootHom A hd hs hp ho K (wordRoot A hs hp b₀ s₀ w k)
        (Multiplicative.ofAdd a))⁻¹ *
      (elementarySelectedRootHom A hd hs hp ho K (wordRoot A hs hp b₀ s₀ w l)
        (Multiplicative.ofAdd b))⁻¹ =
      elementarySelectedRootHom A hd hs hp ho K
        (wordRoot A hs hp b₀ s₀ w (sumRoot A hs k l hpair))
        (Multiplicative.ofAdd ((ε : K) * (a * b))) := by
    apply Subtype.ext
    exact he K a b
  simpa only [rootParameterHom, MonoidHom.comp_apply, map_mul, map_inv] using
    congrArg (originalProjection A hd hs hp ho K i) hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSignedParameters
