import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOrderLower
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalRootFamilyCardinality
import SymmetricSubgroupAsymptotics.CFSGSimpleConjugateFamilyIndex
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootCardinality

/-! The index-square inequality from genuine original-group root
families. The finite root count and uniform commuting-root count are
explicit numerical premises here; exact exceptional installers discharge
them separately. No minimum-index formula or outer-order input is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalRootIndexSquare
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoCoordinateOriginalProjection
open CFSGNormTwoCoordinateOriginalRootFamily CFSGNormTwoCoordinateOriginalRootFamilyCardinality
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateRootElementRange CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoCoordinatePositiveRootCardinality CFSGNormTwoCoordinatePositiveQuotientInjectivity
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoCoordinateRootCentralizerCardinality CFSGNormTwoCoordinateOriginalOrderLower
open CFSGSimpleConjugateFamilyIndex PrimitiveSocleRawStructure
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Finite K] [Nontrivial (Fin r)]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem original_root_line_card (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (θ : Roots A) (hθ : ∀ j, 0 ≤ θ.val j) :
    Nat.card (originalRootLine A hd hs hp ho K i θ) = Nat.card K := by
  let R := rootSubgroup A hd hs hp ho K θ
  let U := PositiveGroup A hd hs hp ho K
  let S := R.subgroupOf U
  let f := (originalProjection A hd hs hp ho K i).comp (positiveInclusion A hd hs hp ho K)
  let e := S.equivMapOfInjective f (originalProjection_positive_injective A hd hs hp ho K p i)
  calc
    Nat.card (originalRootLine A hd hs hp ho K i θ) = Nat.card S :=
      (Nat.card_congr e.toEquiv).symm
    _ = Nat.card R := Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (positive_root_subgroup_le A hd hs hp ho K θ hθ)).toEquiv
    _ = Nat.card K := positive_rootSubgroup_card A hd hs hp ho K θ hθ

theorem original_index_square_lt
    (ε : Fin r → ℤ) (hε : ∀ j, ε j * ε j = 1)
    (hA : ∀ i j, ε i * |A i j| = A j i * ε j)
    (hidentity : ∀ w : List (Fin r), wordUnit A hs hp b₀ s₀ K w ∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _) →
        wordLinear A hs hp b₀ s₀ w = 1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (θ : Roots A) (hθ : ∀ j, 0 ≤ θ.val j)
    (hdom : ∀ j, 0 ≤ integerPairing A θ.val (Pi.single j (1 : ℤ) : Fin r → ℤ))
    (c : ℕ) (hc : ∀ k : Roots A, c ≤ (commutingPositiveRoots A k).card)
    (hR : Nat.card (Roots A) < Nat.card K ^ c)
    (ell : ℕ) (hell : LeastProperIndex (Projective (cartan b₀ s₀) K) ell) :
    ell ^ 2 < Nat.card (Projective (cartan b₀ s₀) K) := by
  let R := originalRootLine A hd hs hp ho K i θ
  have hcardR : Nat.card R = Nat.card K := original_root_line_card A hd hs hp ho K p i θ hθ
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hN : 0 < Nat.card (PositiveRoot A) := by
    letI : Nonempty (PositiveRoot A) := ⟨⟨θ, hθ⟩⟩
    exact Nat.card_pos
  have hB := original_card_lower A hd hs hp ho K ε hε hA hidentity p i
  have hlarge : Nat.card K < Nat.card (Projective (cartan b₀ s₀) K) := by
    have hpw : Nat.card K ^ 2 ≤ Nat.card K ^ (2 * Nat.card (PositiveRoot A)) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hqq : Nat.card K < Nat.card K ^ 2 := by nlinarith
    exact hqq.trans_le (hpw.trans hB)
  have hR0 : R ≠ ⊥ := by
    intro h
    have hh := hcardR
    rw [h, Subgroup.card_bot] at hh
    omega
  have hR1 : R ≠ ⊤ := by
    intro h
    have hh := hcardR
    rw [h, Subgroup.card_top] at hh
    omega
  have hellF := least_index_le_family R hR0 hR1 ell hell
  have hF := original_root_family_card_mul_uniform_commuting_le A hd hs hp ho K i θ hθ hdom c hc
  have hs := square_lt_of_weighted_family (Nat.card K) (Nat.card (PositiveRoot A)) c
    (Nat.card (Roots A)) (Nat.card (originalRootFamily A hd hs hp ho K i θ))
    (Nat.card (Projective (cartan b₀ s₀) K)) (by omega) hR hF hB
  exact (Nat.pow_le_pow_left hellF 2).trans_lt hs

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalRootIndexSquare
