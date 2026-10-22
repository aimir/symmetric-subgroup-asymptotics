import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalRootDegree
import SymmetricSubgroupAsymptotics.CFSGExceptionalGeckIntegralData

/-! Field-size lower bounds for proper subgroup indices in the exact
original and classifier E6/E7/E8 models. All coordinate Cartan transport
is explicit. No published minimum-index formula is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalRootDegree
open CFSG.Models.Chevalley CFSGNormTwoRootPairing
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalNormTwoBases
open CFSGNormTwoCoordinateOriginalRootDegree CFSGNormTwoCoordinatePositiveCenter
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local instance : DecidableEq (Roots CartanMatrix.E₇) := Classical.decEq _
local instance : DecidableEq (Roots CartanMatrix.E₈) := Classical.decEq _

private theorem proper_index_of_coordinate_cartan_eq {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (CFSGIntegerMatrixPairing.rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    [Nontrivial (Fin r)] (K : Type) [Field K] [Finite K]
    {C : Matrix (Fin r) (Fin r) ℤ}
    (hC : CFSGGeckSerreRepresentation.cartan
      (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho) = C)
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective C K)]
    (H : Subgroup (Projective C K)) (hH : H ≠ ⊤) : Nat.card K ≤ H.index := by
  subst C
  obtain ⟨θ, hθ, hdom, _⟩ := exists_root_subgroup_center A hd hs hp ho K
  exact field_card_le_proper_index A hd hs hp ho K p (Classical.arbitrary (Fin r)) θ hθ hdom H hH

theorem serreTypeE6_field_card_le_index (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₆ K)]
    (H : Subgroup (Projective CartanMatrix.E₆ K)) (hH : H ≠ ⊤) : Nat.card K ≤ H.index := by
  have hC := E6_cartan
  change CFSGGeckSerreRepresentation.cartan
    (coordinateBase CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos)
    (coordinateIndexEquiv CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos) = CartanMatrix.E₆ at hC
  exact proper_index_of_coordinate_cartan_eq CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K hC p H hH

theorem typeE6_field_order_le_index (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.E6 q)] (H : Subgroup (CFSG.Models.E6 q)) (hH : H ≠ ⊤) :
    q.order ≤ H.index := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  simpa only [q.card_field] using serreTypeE6_field_card_le_index q.Field q.prime H hH

theorem serreTypeE7_field_card_le_index (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₇ K)]
    (H : Subgroup (Projective CartanMatrix.E₇ K)) (hH : H ≠ ⊤) : Nat.card K ≤ H.index := by
  have hC := E7_cartan
  change CFSGGeckSerreRepresentation.cartan
    (coordinateBase CartanMatrix.E₇ CartanMatrix.E₇_diag CartanMatrix.E₇_transpose
      E7_positive_definite CartanMatrix.E₇_off_diag_nonpos)
    (coordinateIndexEquiv CartanMatrix.E₇ CartanMatrix.E₇_diag CartanMatrix.E₇_transpose
      E7_positive_definite CartanMatrix.E₇_off_diag_nonpos) = CartanMatrix.E₇ at hC
  exact proper_index_of_coordinate_cartan_eq CartanMatrix.E₇ CartanMatrix.E₇_diag
    CartanMatrix.E₇_transpose E7_positive_definite CartanMatrix.E₇_off_diag_nonpos K hC p H hH

theorem typeE7_field_order_le_index (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.E7 q)] (H : Subgroup (CFSG.Models.E7 q)) (hH : H ≠ ⊤) :
    q.order ≤ H.index := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  simpa only [q.card_field] using serreTypeE7_field_card_le_index q.Field q.prime H hH

theorem serreTypeE8_field_card_le_index (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₈ K)]
    (H : Subgroup (Projective CartanMatrix.E₈ K)) (hH : H ≠ ⊤) : Nat.card K ≤ H.index := by
  have hC := E8_cartan
  change CFSGGeckSerreRepresentation.cartan
    (coordinateBase CartanMatrix.E₈ CartanMatrix.E₈_diag CartanMatrix.E₈_transpose
      E8_positive_definite CartanMatrix.E₈_off_diag_nonpos)
    (coordinateIndexEquiv CartanMatrix.E₈ CartanMatrix.E₈_diag CartanMatrix.E₈_transpose
      E8_positive_definite CartanMatrix.E₈_off_diag_nonpos) = CartanMatrix.E₈ at hC
  exact proper_index_of_coordinate_cartan_eq CartanMatrix.E₈ CartanMatrix.E₈_diag
    CartanMatrix.E₈_transpose E8_positive_definite CartanMatrix.E₈_off_diag_nonpos K hC p H hH

theorem typeE8_field_order_le_index (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.E8 q)] (H : Subgroup (CFSG.Models.E8 q)) (hH : H ≠ ⊤) :
    q.order ≤ H.index := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  simpa only [q.card_field] using serreTypeE8_field_card_le_index q.Field q.prime H hH

end SymmetricSubgroupAsymptotics.CFSGExceptionalRootDegree
