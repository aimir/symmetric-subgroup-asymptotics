import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalRootIndexSquare
import SymmetricSubgroupAsymptotics.CFSGExceptionalUniformCommutingRoots
import SymmetricSubgroupAsymptotics.CFSGExceptionalRootCountBound
import SymmetricSubgroupAsymptotics.CFSGExceptionalNormalizerWordIdentity
import SymmetricSubgroupAsymptotics.CFSGExceptionalGeckIntegralData

/-! The strict minimum-index-square bound for the ORIGINAL E6/E7/E8
models. One common root census (at most512) and ten commuting positive
roots suffice in every field, including two elements. No published
minimum-index theorem or group-order formula is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalIndexSquare
open CFSG.Models.Chevalley CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
open CFSGExceptionalNormTwoBases CFSGExceptionalGeckIntegralData
open CFSGSignedCartanReflections CFSGExceptionalNormalizerWordIdentity
open CFSGExceptionalUniformCommutingRoots CFSGExceptionalRootCountBound
open CFSGNormTwoCoordinateOriginalRootIndexSquare CFSGNormTwoCoordinatePositiveCenter
open CFSGNormTwoCoordinateRootCentralizerCardinality PrimitiveSocleRawStructure
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local instance : DecidableEq (Roots CartanMatrix.E₇) := Classical.decEq _
local instance : DecidableEq (Roots CartanMatrix.E₈) := Classical.decEq _

private theorem index_square_of_coordinate_cartan_eq {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (CFSGIntegerMatrixPairing.rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    [Nontrivial (Fin r)] (K : Type) [Field K] [Finite K]
    (ε : Fin r → ℤ) (hε : ∀ j, ε j * ε j = 1)
    (hA : ∀ i j, ε i * |A i j| = A j i * ε j)
    (hidentity : ∀ w : List (Fin r),
      CFSGNormTwoGeckWeylWordDegree.wordUnit A hs hp
        (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho) K w ∈
      Subgroup.normalizer (CFSGNormTwoGeckPositivePGroup.rootGroup A hs hp
        (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho) K false : Set _) →
      CFSGNormTwoGeckWeylLatticeLinear.wordLinear A hs hp
        (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho) w = 1)
    {C : Matrix (Fin r) (Fin r) ℤ}
    (hC : CFSGGeckSerreRepresentation.cartan
      (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho) = C)
    (hRoots : Nat.card (Roots A) ≤ 512)
    (hCommute : ∀ k : Roots A, 10 ≤ (commutingPositiveRoots A k).card)
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective C K)]
    (ell : ℕ) (hell : LeastProperIndex (Projective C K) ell) :
    ell ^ 2 < Nat.card (Projective C K) := by
  subst C
  obtain ⟨θ, hθ, hdom, _⟩ := exists_root_subgroup_center A hd hs hp ho K
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hR : Nat.card (Roots A) < Nat.card K ^ 10 :=
    hRoots.trans_lt ((by decide : 512 < 2 ^ 10).trans_le (Nat.pow_le_pow_left hq 10))
  exact original_index_square_lt A hd hs hp ho K ε hε hA hidentity p
    (Classical.arbitrary (Fin r)) θ hθ hdom 10 hCommute hR ell hell

theorem serreTypeE6_leastIndex_square_lt (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₆ K)]
    (ell : ℕ) (hell : LeastProperIndex (Projective CartanMatrix.E₆ K) ell) :
    ell ^ 2 < Nat.card (Projective CartanMatrix.E₆ K) := by
  have hC := E6_cartan
  change CFSGGeckSerreRepresentation.cartan
    (coordinateBase CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos)
    (coordinateIndexEquiv CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos) = CartanMatrix.E₆ at hC
  exact index_square_of_coordinate_cartan_eq CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K
    E6Signs E6_signs_square E6_signs_cartan (E6_normalizer_word_identity K) hC
    E6_root_card_le E6_uniform_commuting p ell hell

theorem typeE6_leastIndex_square_lt (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.E6 q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.E6 q) ell) :
    ell ^ 2 < Nat.card (CFSG.Models.E6 q) := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  exact serreTypeE6_leastIndex_square_lt q.Field q.prime ell hell

theorem serreTypeE7_leastIndex_square_lt (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₇ K)]
    (ell : ℕ) (hell : LeastProperIndex (Projective CartanMatrix.E₇ K) ell) :
    ell ^ 2 < Nat.card (Projective CartanMatrix.E₇ K) := by
  have hC := E7_cartan
  change CFSGGeckSerreRepresentation.cartan
    (coordinateBase CartanMatrix.E₇ CartanMatrix.E₇_diag CartanMatrix.E₇_transpose
      E7_positive_definite CartanMatrix.E₇_off_diag_nonpos)
    (coordinateIndexEquiv CartanMatrix.E₇ CartanMatrix.E₇_diag CartanMatrix.E₇_transpose
      E7_positive_definite CartanMatrix.E₇_off_diag_nonpos) = CartanMatrix.E₇ at hC
  exact index_square_of_coordinate_cartan_eq CartanMatrix.E₇ CartanMatrix.E₇_diag
    CartanMatrix.E₇_transpose E7_positive_definite CartanMatrix.E₇_off_diag_nonpos K
    E7Signs E7_signs_square E7_signs_cartan (E7_normalizer_word_identity K) hC
    E7_root_card_le E7_uniform_commuting p ell hell

theorem typeE7_leastIndex_square_lt (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.E7 q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.E7 q) ell) :
    ell ^ 2 < Nat.card (CFSG.Models.E7 q) := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  exact serreTypeE7_leastIndex_square_lt q.Field q.prime ell hell

theorem serreTypeE8_leastIndex_square_lt (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₈ K)]
    (ell : ℕ) (hell : LeastProperIndex (Projective CartanMatrix.E₈ K) ell) :
    ell ^ 2 < Nat.card (Projective CartanMatrix.E₈ K) := by
  have hC := E8_cartan
  change CFSGGeckSerreRepresentation.cartan
    (coordinateBase CartanMatrix.E₈ CartanMatrix.E₈_diag CartanMatrix.E₈_transpose
      E8_positive_definite CartanMatrix.E₈_off_diag_nonpos)
    (coordinateIndexEquiv CartanMatrix.E₈ CartanMatrix.E₈_diag CartanMatrix.E₈_transpose
      E8_positive_definite CartanMatrix.E₈_off_diag_nonpos) = CartanMatrix.E₈ at hC
  exact index_square_of_coordinate_cartan_eq CartanMatrix.E₈ CartanMatrix.E₈_diag
    CartanMatrix.E₈_transpose E8_positive_definite CartanMatrix.E₈_off_diag_nonpos K
    E8Signs E8_signs_square E8_signs_cartan (E8_normalizer_word_identity K) hC
    E8_root_card_le E8_uniform_commuting p ell hell

theorem typeE8_leastIndex_square_lt (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.E8 q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.E8 q) ell) :
    ell ^ 2 < Nat.card (CFSG.Models.E8 q) := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  exact serreTypeE8_leastIndex_square_lt q.Field q.prime ell hell

end SymmetricSubgroupAsymptotics.CFSGExceptionalIndexSquare
