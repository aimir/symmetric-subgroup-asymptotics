import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSignedParameters
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateA2ReflectionLabels
import SymmetricSubgroupAsymptotics.CFSGCommutatorParameterRigidity

/-! Actual mixed-sign A2 incidence forces the negative simple parameter
once positive adjacent parameters are fixed. The mixed commutator is a
proved Weyl conjugate of the original positive relation in every field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalMixedA2Rigidity
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

open CFSGNormTwoCoordinateOriginalSignedParameters CFSGNormTwoCoordinateA2ReflectionLabels
open CFSGCommutatorParameterRigidity CFSGNormTwoGeckColumns

theorem rootParameterHom_simple_apply
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r) (a : Multiplicative K) :
    rootParameterHom A hd hs hp ho K i (s₀ j) a =
      simpleParameterHom A hd hs hp ho K i j a := rfl

def negativeParameterHom [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r) :
    Multiplicative K →* Projective (cartan b₀ s₀) K :=
  rootParameterHom A hd hs hp ho K i (negativeIndex A hs hp (s₀ j))

 def sumParameterHom [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i j k : Fin r) (hjk : A j k = -1) : Multiplicative K →* Projective (cartan b₀ s₀) K :=
  rootParameterHom A hd hs hp ho K i (simplePairSum A hd hs hp ho j k hjk)

 theorem mixed_simple_commutator_sign
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j k : Fin r) (hjk : A j k = -1) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ a b : K,
      negativeParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a) *
        sumParameterHom A hd hs hp ho K i j k hjk (Multiplicative.ofAdd b) *
        (negativeParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a))⁻¹ *
        (sumParameterHom A hd hs hp ho K i j k hjk (Multiplicative.ofAdd b))⁻¹ =
      simpleParameterHom A hd hs hp ho K i k (Multiplicative.ofAdd ((ε : K) * (a * b))) := by
  obtain ⟨ε, hε, he⟩ := original_word_pair_commutator_sign A hd hs hp ho K i [j] (s₀ j) (s₀ k)
    (simple_root_nonnegative A hd hs hp ho j) (simple_root_nonnegative A hd hs hp ho k)
    (simple_pairing_eq_neg_one A hd hs hp ho j k hjk)
  have hsum : sumRoot A hs (s₀ j) (s₀ k)
      (simple_pairing_eq_neg_one A hd hs hp ho j k hjk) =
        simplePairSum A hd hs hp ho j k hjk := rfl
  rw [hsum] at he
  rw [reflect_simple_self A hd hs hp ho j,
    reflect_adjacent_simple A hd hs hp ho j k hjk,
    reflect_simple_sum A hd hs hp ho j k hjk] at he
  refine ⟨ε, hε, ?_⟩
  intro a b
  have hab := he a b
  rw [rootParameterHom_simple_apply A hd hs hp ho K i k] at hab
  exact hab

 theorem simple_sum_parameter_fixed
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j k : Fin r) (hjk : A j k = -1)
    (f : MulAut (Projective (cartan b₀ s₀) K))
    (hj : ∀ a, f (simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a)) =
      simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a))
    (hk : ∀ a, f (simpleParameterHom A hd hs hp ho K i k (Multiplicative.ofAdd a)) =
      simpleParameterHom A hd hs hp ho K i k (Multiplicative.ofAdd a)) :
    ∀ a, f (sumParameterHom A hd hs hp ho K i j k hjk (Multiplicative.ofAdd a)) =
      sumParameterHom A hd hs hp ho K i j k hjk (Multiplicative.ofAdd a) := by
  obtain ⟨ε, hε, he⟩ := original_word_pair_commutator_sign A hd hs hp ho K i [] (s₀ j) (s₀ k)
    (simple_root_nonnegative A hd hs hp ho j) (simple_root_nonnegative A hd hs hp ho k)
    (simple_pairing_eq_neg_one A hd hs hp ho j k hjk)
  have hεsq : (ε : K) * (ε : K) = 1 := by rcases hε with rfl | rfl <;> norm_num
  intro a
  have harg : (ε : K) * (((ε : K) * a) * 1) = a := by
    rw [mul_one, ← mul_assoc, hεsq, one_mul]
  have hcomm : simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd ((ε : K) * a)) *
      simpleParameterHom A hd hs hp ho K i k (Multiplicative.ofAdd 1) *
      (simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd ((ε : K) * a)))⁻¹ *
      (simpleParameterHom A hd hs hp ho K i k (Multiplicative.ofAdd 1))⁻¹ =
      sumParameterHom A hd hs hp ho K i j k hjk (Multiplicative.ofAdd a) := by
    simpa only [wordRoot, harg] using he ((ε : K) * a) 1
  calc
    _ = f (simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd ((ε : K) * a)) *
        simpleParameterHom A hd hs hp ho K i k (Multiplicative.ofAdd 1) *
        (simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd ((ε : K) * a)))⁻¹ *
        (simpleParameterHom A hd hs hp ho K i k (Multiplicative.ofAdd 1))⁻¹) := congrArg f hcomm.symm
    _ = _ := by simpa only [map_mul, map_inv, hj, hk] using hcomm

 theorem negative_simple_parameter_fixed [Finite K] [Nontrivial (Fin r)]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j k : Fin r) (hjk : A j k = -1)
    (f : MulAut (Projective (cartan b₀ s₀) K))
    (hj : ∀ a, f (simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a)) =
      simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a))
    (hk : ∀ a, f (simpleParameterHom A hd hs hp ho K i k (Multiplicative.ofAdd a)) =
      simpleParameterHom A hd hs hp ho K i k (Multiplicative.ofAdd a))
    (hneg : (negativeParameterHom A hd hs hp ho K i j).range.map f.toMonoidHom =
      (negativeParameterHom A hd hs hp ho K i j).range) :
    ∀ a, f (negativeParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a)) =
      negativeParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a) := by
  obtain ⟨ε, hε, he⟩ := mixed_simple_commutator_sign A hd hs hp ho K i j k hjk
  have hc : (ε : K) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hu : Function.Injective (fun a : K =>
      simpleParameterHom A hd hs hp ho K i k (Multiplicative.ofAdd a)) :=
    (simpleParameterHom_injective A hd hs hp ho K p i k).comp Multiplicative.ofAdd.injective
  apply fixed_parameter_of_mixed_commutator _ _ _ hu (ε : K) hc he f.toMonoidHom hk
    (simple_sum_parameter_fixed A hd hs hp ho K i j k hjk f hj hk)
  intro a
  have ha : f (negativeParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a)) ∈
      (negativeParameterHom A hd hs hp ho K i j).range := by
    rw [← hneg]
    exact ⟨_, ⟨Multiplicative.ofAdd a, rfl⟩, rfl⟩
  obtain ⟨b, hb⟩ := ha
  exact ⟨b.toAdd, hb.symm⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalMixedA2Rigidity
