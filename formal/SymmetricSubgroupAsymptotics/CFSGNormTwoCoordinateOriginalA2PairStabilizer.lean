import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalA2FieldRecognition
import SymmetricSubgroupAsymptotics.CFSGCommutatorParameterRange

/-! Stabilizing two actual original adjacent positive root groups forces
stability of their sum-root group and a common field automorphism. The
third-root stability premise is discharged using the proved original
commutator relation; no root-recognition premise is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalA2PairStabilizer
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoCoordinateOriginalProjection
open CFSGNormTwoCoordinateOriginalRootDegree CFSGNormTwoCoordinatePositivePairCollecting
open CFSGNormTwoCoordinateElementaryRootParameters CFSGRootParameterAutomorphism
open CFSGFieldScaledRootHom CFSGCommutatorParameterRange
open CFSGNormTwoCoordinateOriginalA2FieldRecognition
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem positive_A2_sum_root_stable
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (k l : Roots A) (hk : ∀ j, 0 ≤ k.val j) (hl : ∀ j, 0 ≤ l.val j)
    (hpair : integerPairing A k.val l.val = -1)
    (f : MulAut (Projective (cartan b₀ s₀) K))
    (hfk : (originalSelectedHom A hd hs hp ho K i k hk).range.map f.toMonoidHom =
      (originalSelectedHom A hd hs hp ho K i k hk).range)
    (hfl : (originalSelectedHom A hd hs hp ho K i l hl).range.map f.toMonoidHom =
      (originalSelectedHom A hd hs hp ho K i l hl).range) :
    (originalSelectedHom A hd hs hp ho K i (sumRoot A hs k l hpair)
      (fun j => add_nonneg (hk j) (hl j))).range.map f.toMonoidHom =
      (originalSelectedHom A hd hs hp ho K i (sumRoot A hs k l hpair)
      (fun j => add_nonneg (hk j) (hl j))).range := by
  let u := originalSelectedHom A hd hs hp ho K i k hk
  let v := originalSelectedHom A hd hs hp ho K i l hl
  let z := originalSelectedHom A hd hs hp ho K i (sumRoot A hs k l hpair)
    (fun j => add_nonneg (hk j) (hl j))
  obtain ⟨ε, hε, he⟩ := original_positive_pair_commutator A hd hs hp ho K i k l hk hl hpair
  have hc : (ε : K) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hcomm : ∀ a b : K, u (Multiplicative.ofAdd a) * v (Multiplicative.ofAdd b) *
      (u (Multiplicative.ofAdd a))⁻¹ * (v (Multiplicative.ofAdd b))⁻¹ =
        scaledHom z (ε : K) (Multiplicative.ofAdd (a * b)) := he
  have hstable := commutator_range_map u v (scaledHom z (ε : K)) hcomm
    f.toMonoidHom hfk hfl
  simpa only [scaledHom_range z (ε : K) hc] using hstable

 theorem positive_A2_pair_stabilizer_semilinear [Finite K] [Nontrivial (Fin r)]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (k l : Roots A) (hk : ∀ j, 0 ≤ k.val j) (hl : ∀ j, 0 ≤ l.val j)
    (hpair : integerPairing A k.val l.val = -1)
    (f : MulAut (Projective (cartan b₀ s₀) K))
    (hfk : (originalSelectedHom A hd hs hp ho K i k hk).range.map f.toMonoidHom =
      (originalSelectedHom A hd hs hp ho K i k hk).range)
    (hfl : (originalSelectedHom A hd hs hp ho K i l hl).range.map f.toMonoidHom =
      (originalSelectedHom A hd hs hp ho K i l hl).range) :
    ∃ (σ : K ≃+* K) (c d : K), c ≠ 0 ∧ d ≠ 0 ∧ ∀ a : K,
      f (originalSelectedHom A hd hs hp ho K i k hk (Multiplicative.ofAdd a)) =
        originalSelectedHom A hd hs hp ho K i k hk (Multiplicative.ofAdd (c * σ a)) ∧
      f (originalSelectedHom A hd hs hp ho K i l hl (Multiplicative.ofAdd a)) =
        originalSelectedHom A hd hs hp ho K i l hl (Multiplicative.ofAdd (d * σ a)) := by
  exact positive_A2_root_stabilizer_semilinear A hd hs hp ho K p i k l hk hl hpair f hfk hfl
    (positive_A2_sum_root_stable A hd hs hp ho K i k l hk hl hpair f hfk hfl)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalA2PairStabilizer
