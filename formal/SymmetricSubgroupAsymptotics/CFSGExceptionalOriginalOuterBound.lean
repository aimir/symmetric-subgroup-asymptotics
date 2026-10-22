import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOuterBound
import SymmetricSubgroupAsymptotics.CFSGExceptionalNormalizerWordIdentity
import SymmetricSubgroupAsymptotics.CFSGExceptionalGeckIntegralData
import SymmetricSubgroupAsymptotics.CFSGExceptionalCartanNeighbors
import SymmetricSubgroupAsymptotics.CFSGExceptionalDiagramCardinality
import SymmetricSubgroupAsymptotics.CFSGCartanE6PowerIndex
import SymmetricSubgroupAsymptotics.CFSGCartanE7PowerIndex
import SymmetricSubgroupAsymptotics.CFSGCartanE8PowerIndex
import Mathlib.Tactic.Ring

/-! Actual outer-automorphism bounds for the ORIGINAL pinned untwisted
E6/E7/E8 Serre projective models. Every root, normalizer-word, graph and
finite Cartan-image premise is discharged. The E6 literal Cartan-index
version is retained for the sharper field-of-two consumer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalOriginalOuterBound
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGExceptionalCartanPositiveDefinite
open CFSGExceptionalNormTwoBases CFSGExceptionalGeckIntegralData
open CFSGSignedCartanReflections CFSGExceptionalNormalizerWordIdentity
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoCoordinatePositiveCenter CFSGNormTwoCoordinateOriginalOuterBound
open CFSGExceptionalCartanConnected CFSGExceptionalCartanNeighbors CFSGExceptionalDiagramCardinality
open CFSGExceptionalDiagramAutomorphisms CFSGIntegerMatrixPowerHom PrimitiveSocleRawStructure
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local instance : DecidableEq (Roots CartanMatrix.E₇) := Classical.decEq _
local instance : DecidableEq (Roots CartanMatrix.E₈) := Classical.decEq _

private theorem outer_bound_of_coordinate_cartan_eq {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    [Nontrivial (Fin r)] (K : Type) [Field K] [Finite K]
    (ε : Fin r → ℤ) (hε : ∀ j, ε j * ε j = 1)
    (hA : ∀ i j, ε i * |A i j| = A j i * ε j)
    (hidentity : ∀ w : List (Fin r), wordUnit A hs hp
      (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho) K w ∈
      Subgroup.normalizer (rootGroup A hs hp (coordinateBase A hd hs hp ho)
        (coordinateIndexEquiv A hd hs hp ho) K false : Set _) →
      wordLinear A hs hp (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho) w = 1)
    (j₀ k₀ : Fin r) (hjk : A j₀ k₀ = -1)
    (hconn : ∀ j, Relation.ReflTransGen (fun a b => A a b ≠ 0) j₀ j)
    (hneighbors : ∀ j, ∃ k, A j k = -1)
    {C : Matrix (Fin r) (Fin r) ℤ}
    (hC : cartan (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho) = C)
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective C K)] :
    Nat.card (Outer (Projective C K)) ≤
      ((powerHom (G := Kˣ) A).range.index * Nat.card (K ≃+* K)) * Nat.card (diagramGroup A) := by
  subst C
  let i : Fin r := Classical.arbitrary _
  obtain ⟨θ, hθ, hdom, _⟩ := exists_root_subgroup_center A hd hs hp ho K
  exact original_outer_card_le A hd hs hp ho K ε hε hA hidentity p i θ hθ hdom
    j₀ k₀ hjk hconn hneighbors

theorem serreTypeE6_outer_card_le_cartan (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₆ K)] :
    Nat.card (Outer (Projective CartanMatrix.E₆ K)) ≤ ((powerHom (G := Kˣ) CartanMatrix.E₆).range.index * Nat.card (K ≃+* K)) * 2 := by
  have hC := E6_cartan
  change cartan
    (coordinateBase CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos)
    (coordinateIndexEquiv CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos) = CartanMatrix.E₆ at hC
  have h := outer_bound_of_coordinate_cartan_eq CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
    K E6Signs E6_signs_square E6_signs_cartan (E6_normalizer_word_identity K)
    0 2 (by decide) (E6_connected 0) E6_neighbor hC p
  exact h.trans (Nat.mul_le_mul_left _ E6_diagram_card_le)

theorem serreTypeE6_outer_card_le (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₆ K)] :
    Nat.card (Outer (Projective CartanMatrix.E₆ K)) ≤ 6 * Nat.card (K ≃+* K) := by
  calc
    _ ≤ ((powerHom (G := Kˣ) CartanMatrix.E₆).range.index * Nat.card (K ≃+* K)) * 2 :=
      serreTypeE6_outer_card_le_cartan K p
    _ ≤ (3 * Nat.card (K ≃+* K)) * 2 :=
      Nat.mul_le_mul_right 2 (Nat.mul_le_mul_right _ (CFSGCartanE6PowerIndex.range_index_le K))
    _ = 6 * Nat.card (K ≃+* K) := by ring

theorem serreTypeE7_outer_card_le_cartan (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₇ K)] :
    Nat.card (Outer (Projective CartanMatrix.E₇ K)) ≤ ((powerHom (G := Kˣ) CartanMatrix.E₇).range.index * Nat.card (K ≃+* K)) * 1 := by
  have hC := E7_cartan
  change cartan
    (coordinateBase CartanMatrix.E₇ CartanMatrix.E₇_diag CartanMatrix.E₇_transpose
      E7_positive_definite CartanMatrix.E₇_off_diag_nonpos)
    (coordinateIndexEquiv CartanMatrix.E₇ CartanMatrix.E₇_diag CartanMatrix.E₇_transpose
      E7_positive_definite CartanMatrix.E₇_off_diag_nonpos) = CartanMatrix.E₇ at hC
  have h := outer_bound_of_coordinate_cartan_eq CartanMatrix.E₇ CartanMatrix.E₇_diag
    CartanMatrix.E₇_transpose E7_positive_definite CartanMatrix.E₇_off_diag_nonpos
    K E7Signs E7_signs_square E7_signs_cartan (E7_normalizer_word_identity K)
    0 2 (by decide) (E7_connected 0) E7_neighbor hC p
  exact h.trans (Nat.mul_le_mul_left _ E7_diagram_card_le)

theorem serreTypeE7_outer_card_le (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₇ K)] :
    Nat.card (Outer (Projective CartanMatrix.E₇ K)) ≤ 2 * Nat.card (K ≃+* K) := by
  calc
    _ ≤ ((powerHom (G := Kˣ) CartanMatrix.E₇).range.index * Nat.card (K ≃+* K)) * 1 :=
      serreTypeE7_outer_card_le_cartan K p
    _ ≤ (2 * Nat.card (K ≃+* K)) * 1 :=
      Nat.mul_le_mul_right 1 (Nat.mul_le_mul_right _ (CFSGCartanE7PowerIndex.range_index_le K))
    _ = 2 * Nat.card (K ≃+* K) := by ring

theorem serreTypeE8_outer_card_le_cartan (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₈ K)] :
    Nat.card (Outer (Projective CartanMatrix.E₈ K)) ≤ ((powerHom (G := Kˣ) CartanMatrix.E₈).range.index * Nat.card (K ≃+* K)) * 1 := by
  have hC := E8_cartan
  change cartan
    (coordinateBase CartanMatrix.E₈ CartanMatrix.E₈_diag CartanMatrix.E₈_transpose
      E8_positive_definite CartanMatrix.E₈_off_diag_nonpos)
    (coordinateIndexEquiv CartanMatrix.E₈ CartanMatrix.E₈_diag CartanMatrix.E₈_transpose
      E8_positive_definite CartanMatrix.E₈_off_diag_nonpos) = CartanMatrix.E₈ at hC
  have h := outer_bound_of_coordinate_cartan_eq CartanMatrix.E₈ CartanMatrix.E₈_diag
    CartanMatrix.E₈_transpose E8_positive_definite CartanMatrix.E₈_off_diag_nonpos
    K E8Signs E8_signs_square E8_signs_cartan (E8_normalizer_word_identity K)
    0 2 (by decide) (E8_connected 0) E8_neighbor hC p
  exact h.trans (Nat.mul_le_mul_left _ E8_diagram_card_le)

theorem serreTypeE8_outer_card_le (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₈ K)] :
    Nat.card (Outer (Projective CartanMatrix.E₈ K)) ≤ 1 * Nat.card (K ≃+* K) := by
  calc
    _ ≤ ((powerHom (G := Kˣ) CartanMatrix.E₈).range.index * Nat.card (K ≃+* K)) * 1 :=
      serreTypeE8_outer_card_le_cartan K p
    _ ≤ (1 * Nat.card (K ≃+* K)) * 1 :=
      Nat.mul_le_mul_right 1 (Nat.mul_le_mul_right _ (CFSGCartanE8PowerIndex.range_index_le K))
    _ = 1 * Nat.card (K ≃+* K) := by ring

end SymmetricSubgroupAsymptotics.CFSGExceptionalOriginalOuterBound
