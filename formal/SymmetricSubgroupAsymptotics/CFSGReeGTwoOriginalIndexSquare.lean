import SymmetricSubgroupAsymptotics.CFSGReeGTwoDerivedIndex
import SymmetricSubgroupAsymptotics.CFSGReeGTwoIndexPointUpper
import SymmetricSubgroupAsymptotics.CFSGReeGTwoIndexSquareNumerics

/-! The strict index square for the pinned original Ree model. The
order lower bound retains the full fixed group's possible derived
index four; the point stabilizer is pulled back to the actual derived
group before transport to the original model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalIndexSquare
open PrimitiveSocleRawStructure

theorem original_index_square (m : ℕ) (hm : 1≤m) (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.ReeG2 m) ell) :
    ell^2 < Nat.card (CFSG.Models.ReeG2 m) := by
  have hq : 27≤3^(2*m+1) :=
    Nat.pow_le_pow_right (by decide : 1≤3) (by omega : 3≤2*m+1)
  exact CFSGReeGTwoIndexSquareNumerics.index_square_lt
    (3^(2*m+1)) ell (Nat.card (CFSG.Models.ReeG2 m)) (by omega)
    (CFSGReeGTwoIndexPointUpper.original_leastProperIndex_le m hm ell hell)
    (CFSGReeGTwoDerivedIndex.original_order_lower m hm)

end SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalIndexSquare
