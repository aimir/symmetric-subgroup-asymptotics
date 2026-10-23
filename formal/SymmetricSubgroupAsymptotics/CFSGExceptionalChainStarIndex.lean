import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalChainStarRows
import SymmetricSubgroupAsymptotics.CFSGExceptionalGeckIntegralData

/-! Actual field-power proper-index bounds for the ORIGINAL E6/E7/E8
projective Serre models: q², q³ and q⁵ respectively. Their concrete
integral chain stars discharge the chart, injection and row equations.
Every field characteristic is retained. No index formula or source
recognition assumption is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGExceptionalCartanPositiveDefinite
open CFSGExceptionalChainStarData
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local instance : DecidableEq (Roots CartanMatrix.E₇) := Classical.decEq _
local instance : DecidableEq (Roots CartanMatrix.E₈) := Classical.decEq _

private theorem chain_star_index_of_coordinate_cartan_eq {r n : ℕ}
    (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    [Nontrivial (Fin r)] (K : Type) [Field K] [Finite K]
    (S : ChainStar A n) (hn:0<n) {B : Matrix (Fin r) (Fin r) ℤ}
    (hB : cartan (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho)=B)
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective B K)]
    (H : Subgroup (Projective B K)) (hH:H≠⊤) : Nat.card K^(n+1)≤H.index := by
  subst B
  exact CFSGNormTwoCoordinateOriginalChainStarRows.field_power_le_proper_index
    A hd hs hp ho K S (Classical.arbitrary (Fin r)) p hn H hH

theorem serreTypeE6_field_square_le_index (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₆ K)]
    (H : Subgroup (Projective CartanMatrix.E₆ K)) (hH:H≠⊤) : Nat.card K^2≤H.index := by
  exact chain_star_index_of_coordinate_cartan_eq CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K E6 (by decide) (B:=CartanMatrix.E₆)
    (by
      ext i j
      exact coordinate_cartan_transpose CartanMatrix.E₆ CartanMatrix.E₆_diag
        CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos i j) p H hH

theorem typeE6_field_square_le_index (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.E6 q)] (H : Subgroup (CFSG.Models.E6 q)) (hH:H≠⊤) :
    q.order^2≤H.index := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  simpa only [q.card_field] using serreTypeE6_field_square_le_index q.Field q.prime H hH

theorem serreTypeE7_field_cube_le_index (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₇ K)]
    (H : Subgroup (Projective CartanMatrix.E₇ K)) (hH:H≠⊤) : Nat.card K^3≤H.index := by
  exact chain_star_index_of_coordinate_cartan_eq CartanMatrix.E₇ CartanMatrix.E₇_diag
    CartanMatrix.E₇_transpose E7_positive_definite CartanMatrix.E₇_off_diag_nonpos K E7 (by decide) (B:=CartanMatrix.E₇)
    (by
      ext i j
      exact coordinate_cartan_transpose CartanMatrix.E₇ CartanMatrix.E₇_diag
        CartanMatrix.E₇_transpose E7_positive_definite CartanMatrix.E₇_off_diag_nonpos i j) p H hH

theorem typeE7_field_cube_le_index (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.E7 q)] (H : Subgroup (CFSG.Models.E7 q)) (hH:H≠⊤) :
    q.order^3≤H.index := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  simpa only [q.card_field] using serreTypeE7_field_cube_le_index q.Field q.prime H hH

theorem serreTypeE8_field_fifth_le_index (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₈ K)]
    (H : Subgroup (Projective CartanMatrix.E₈ K)) (hH:H≠⊤) : Nat.card K^5≤H.index := by
  exact chain_star_index_of_coordinate_cartan_eq CartanMatrix.E₈ CartanMatrix.E₈_diag
    CartanMatrix.E₈_transpose E8_positive_definite CartanMatrix.E₈_off_diag_nonpos K E8 (by decide) (B:=CartanMatrix.E₈)
    (by
      ext i j
      exact coordinate_cartan_transpose CartanMatrix.E₈ CartanMatrix.E₈_diag
        CartanMatrix.E₈_transpose E8_positive_definite CartanMatrix.E₈_off_diag_nonpos i j) p H hH

theorem typeE8_field_fifth_le_index (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.E8 q)] (H : Subgroup (CFSG.Models.E8 q)) (hH:H≠⊤) :
    q.order^5≤H.index := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  simpa only [q.card_field] using serreTypeE8_field_fifth_le_index q.Field q.prime H hH

end SymmetricSubgroupAsymptotics.CFSGReduction
