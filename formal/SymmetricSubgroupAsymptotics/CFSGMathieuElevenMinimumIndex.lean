import SymmetricSubgroupAsymptotics.CFSGMathieuElevenActualIndexSquare
import SymmetricSubgroupAsymptotics.PrimePeriodSimpleQuotientIndex

/-! The certified actual order 7920 is divisible by eleven. Inherited
pinned simplicity makes every proper coset action faithful, so its
degree is at least eleven. The existing actual eleven-point stabilizer
then identifies the least proper index. No outer-order bound is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuElevenMinimumIndex
open CFSG.Models.Presentations.M11 PrimitiveSocleRawStructure

theorem proper_index_ge_eleven [Finite Model] [IsSimpleGroup Model]
    (H : Subgroup Model) (hH : H ≠ ⊤) : 11 ≤ H.index := by
  apply PrimePeriodSimpleQuotientIndex.prime_le_proper_index 11
    (by decide : Nat.Prime 11) ?_ H hH
  rw [CFSGMathieuElevenActualEquivalence.card]
  decide

theorem least_index_eq_eleven [Finite Model] [IsSimpleGroup Model]
    (ell : ℕ) (hell : LeastProperIndex Model ell) : ell = 11 := by
  apply Nat.le_antisymm (CFSGMathieuElevenActualIndexSquare.least_index_le_eleven ell hell)
  obtain ⟨H,hH,hindex⟩ := hell.1
  rw [←hindex]
  exact proper_index_ge_eleven H hH

end SymmetricSubgroupAsymptotics.CFSGMathieuElevenMinimumIndex
