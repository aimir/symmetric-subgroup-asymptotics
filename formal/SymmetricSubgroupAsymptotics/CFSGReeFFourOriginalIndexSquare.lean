import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalMiddleParabolic
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOrderLower
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex

/-! The strict least-index square on the pinned original Ree model.
The original proper parabolic keeps the full quotient kernel, and the
opposed Sylow lower bound belongs to that same model. Tits is separate. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalIndexSquare
open PrimitiveSocleRawStructure CFSGReeFFourOriginalMiddleParabolic

theorem original_leastProperIndex_le (m : ℕ) (hm : 0<m) (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.ReeF4 m) ell) :
    ell ≤ CFSGReeFFourParabolicIndexNumerics.indexUpper (2^(2*m+1)) :=
  (hell.2 (originalMiddleParabolic m hm) (originalMiddleParabolic_ne_top m hm)).trans
    (originalMiddleParabolic_index_le m hm)

theorem original_index_square (m : ℕ) (hm : 0<m) (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.ReeF4 m) ell) :
    ell^2 < Nat.card (CFSG.Models.ReeF4 m) := by
  have hq : 4≤2^(2*m+1) :=
    (by decide : 4≤(2 : ℕ)^2).trans
      (Nat.pow_le_pow_right (by decide) (by omega : 2≤2*m+1))
  exact ((Nat.pow_le_pow_left (original_leastProperIndex_le m hm ell hell) 2).trans_lt
    (CFSGReeFFourParabolicIndexNumerics.indexUpper_square_lt _ hq)).trans_le
      (CFSGReeFFourOriginalOrderLower.original_ree_order_ge m hm)

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalIndexSquare
