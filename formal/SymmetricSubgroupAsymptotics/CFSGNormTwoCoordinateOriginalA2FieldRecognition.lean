import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalRootDegree
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePairCollecting
import SymmetricSubgroupAsymptotics.CFSGRootParameterAutomorphism
import SymmetricSubgroupAsymptotics.CFSGFieldScaledRootHom

/-! Semilinearity on ACTUAL original positive A2 root pairs. The proved
integral commutator sign is absorbed in the sum-root parameter. Thus an
actual group automorphism stabilizing the three displayed root groups
has the same field automorphism on the two original root parameters.
No commutator or source-faithfulness hypothesis is added. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalA2FieldRecognition
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoCoordinateOriginalProjection
open CFSGNormTwoCoordinateOriginalRootDegree CFSGNormTwoCoordinatePositivePairCollecting
open CFSGNormTwoCoordinateElementaryRootParameters CFSGRootParameterAutomorphism
open CFSGFieldScaledRootHom
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

 theorem original_positive_pair_commutator
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (k l : Roots A) (hk : ∀ j, 0 ≤ k.val j) (hl : ∀ j, 0 ≤ l.val j)
    (hpair : integerPairing A k.val l.val = -1) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ a b : K,
      originalSelectedHom A hd hs hp ho K i k hk (Multiplicative.ofAdd a) *
        originalSelectedHom A hd hs hp ho K i l hl (Multiplicative.ofAdd b) *
        (originalSelectedHom A hd hs hp ho K i k hk (Multiplicative.ofAdd a))⁻¹ *
        (originalSelectedHom A hd hs hp ho K i l hl (Multiplicative.ofAdd b))⁻¹ =
      originalSelectedHom A hd hs hp ho K i (sumRoot A hs k l hpair)
        (fun j => add_nonneg (hk j) (hl j)) (Multiplicative.ofAdd ((ε : K) * (a * b))) := by
  obtain ⟨ε, hε, he⟩ := positive_pair_commutator_sign A hd hs hp ho k l hk hl hpair
  refine ⟨ε, hε, ?_⟩
  intro a b
  simp only [originalSelectedHom_apply]
  have hcan : elementarySelectedRootHom A hd hs hp ho K k (Multiplicative.ofAdd a) *
      elementarySelectedRootHom A hd hs hp ho K l (Multiplicative.ofAdd b) *
      (elementarySelectedRootHom A hd hs hp ho K k (Multiplicative.ofAdd a))⁻¹ *
      (elementarySelectedRootHom A hd hs hp ho K l (Multiplicative.ofAdd b))⁻¹ =
        elementarySelectedRootHom A hd hs hp ho K (sumRoot A hs k l hpair)
          (Multiplicative.ofAdd ((ε : K) * (a * b))) := by
    apply Subtype.ext
    exact he K a b
  simpa only [map_mul, map_inv] using congrArg (originalProjection A hd hs hp ho K i) hcan

theorem positive_A2_root_stabilizer_semilinear [Finite K] [Nontrivial (Fin r)]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (k l : Roots A) (hk : ∀ j, 0 ≤ k.val j) (hl : ∀ j, 0 ≤ l.val j)
    (hpair : integerPairing A k.val l.val = -1)
    (f : MulAut (Projective (cartan b₀ s₀) K))
    (hfk : (originalSelectedHom A hd hs hp ho K i k hk).range.map f.toMonoidHom =
      (originalSelectedHom A hd hs hp ho K i k hk).range)
    (hfl : (originalSelectedHom A hd hs hp ho K i l hl).range.map f.toMonoidHom =
      (originalSelectedHom A hd hs hp ho K i l hl).range)
    (hfsum : (originalSelectedHom A hd hs hp ho K i (sumRoot A hs k l hpair)
      (fun j => add_nonneg (hk j) (hl j))).range.map f.toMonoidHom =
      (originalSelectedHom A hd hs hp ho K i (sumRoot A hs k l hpair)
      (fun j => add_nonneg (hk j) (hl j))).range) :
    ∃ (σ : K ≃+* K) (c d : K), c ≠ 0 ∧ d ≠ 0 ∧ ∀ a : K,
      f (originalSelectedHom A hd hs hp ho K i k hk (Multiplicative.ofAdd a)) =
        originalSelectedHom A hd hs hp ho K i k hk (Multiplicative.ofAdd (c * σ a)) ∧
      f (originalSelectedHom A hd hs hp ho K i l hl (Multiplicative.ofAdd a)) =
        originalSelectedHom A hd hs hp ho K i l hl (Multiplicative.ofAdd (d * σ a)) := by
  let u := originalSelectedHom A hd hs hp ho K i k hk
  let v := originalSelectedHom A hd hs hp ho K i l hl
  let z := originalSelectedHom A hd hs hp ho K i (sumRoot A hs k l hpair)
    (fun j => add_nonneg (hk j) (hl j))
  have hu : Function.Injective u := originalSelectedHom_injective A hd hs hp ho K p i k hk
  have hv : Function.Injective v := originalSelectedHom_injective A hd hs hp ho K p i l hl
  have hz : Function.Injective z := originalSelectedHom_injective A hd hs hp ho K p i _ _
  obtain ⟨ε, hε, he⟩ := original_positive_pair_commutator A hd hs hp ho K i k l hk hl hpair
  have hc : (ε : K) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  let w := scaledHom z (ε : K)
  have hw : Function.Injective w := scaledHom_injective z hz (ε : K) hc
  have hfw : w.range.map f.toMonoidHom = w.range := by
    change (scaledHom z (ε : K)).range.map f.toMonoidHom = (scaledHom z (ε : K)).range
    rw [scaledHom_range z (ε : K) hc]
    exact hfsum
  have hcomm : ∀ a b : K, u (Multiplicative.ofAdd a) * v (Multiplicative.ofAdd b) *
      (u (Multiplicative.ofAdd a))⁻¹ * (v (Multiplicative.ofAdd b))⁻¹ =
        w (Multiplicative.ofAdd (a * b)) := he
  obtain ⟨σ, hσ⟩ := common_field_automorphism_of_commutator u v w hu hv hw hcomm f hfk hfl hfw
  let c := parameterAut u hu f hfk 1
  let d := parameterAut v hv f hfl 1
  have hc0 : c ≠ 0 := by
    intro he
    exact one_ne_zero ((parameterAut u hu f hfk).injective
      (he.trans (parameterAut u hu f hfk).map_zero.symm))
  have hd0 : d ≠ 0 := by
    intro he
    exact one_ne_zero ((parameterAut v hv f hfl).injective
      (he.trans (parameterAut v hv f hfl).map_zero.symm))
  exact ⟨σ, c, d, hc0, hd0, fun a => ⟨(hσ a).1, (hσ a).2.1⟩⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalA2FieldRecognition
