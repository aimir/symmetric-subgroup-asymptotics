import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalProjection
import SymmetricSubgroupAsymptotics.CFSGGTwoIndexPointUpper
import SymmetricSubgroupAsymptotics.CFSGGTwoIndexSquareNumerics

/-! The strict least-proper-index square on the ORIGINAL pinned simple
G2 model. Both the singular-ray upper index and the q^12 lower order
are proved on that same model; no recognition or order-formula input
is retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalIndexSquare
open PrimitiveSocleRawStructure CFSG.Models.Chevalley

theorem original_index_square (K : Type) [Field K] [Finite K]
    (hcard : 3 ≤ Nat.card K) [IsSimpleGroup (Projective CartanMatrix.G₂ K)]
    (ell : ℕ) (hell : LeastProperIndex (Projective CartanMatrix.G₂ K) ell) :
    ell^2 < Nat.card (Projective CartanMatrix.G₂ K) :=
  CFSGGTwoIndexSquareNumerics.index_square_lt _ _ _ hcard
    (CFSGGTwoIndexPointUpper.original_leastProperIndex_lt K hcard ell hell)
    (CFSGGTwoD4GeckOriginalProjection.original_order_lower K)

theorem typeGTwo_index_square (q : CFSG.PrimePower) (hsmall : q.order ≠ 2)
    [IsSimpleGroup (CFSG.Models.G2 q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.G2 q) ell) :
    ell^2 < Nat.card (CFSG.Models.G2 q) := by
  have hq2 : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hq3 : 3 ≤ Nat.card q.Field := by rw [q.card_field]; omega
  exact original_index_square q.Field hq3 ell hell

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalIndexSquare
