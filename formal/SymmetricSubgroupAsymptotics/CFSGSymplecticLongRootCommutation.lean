import SymmetricSubgroupAsymptotics.CFSGSymplecticInitialRootLines
import SymmetricSubgroupAsymptotics.CFSGTwistedMonomialRootTransport

/-! The short factor in the cleaned mixed Weyl word commutes with all
upper long roots except coordinate zero, and with the lower long root
at coordinate zero. These are exact natural matrix identities. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSGMonomialUnitRootAction CFSGTwistedMonomialRootTransport

theorem initialShort_commutes_upper_long (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (j : Fin (r + 1)) (hj : j ≠ 0) (a b : K) :
    Commute (initialShortRoot K r a).val
      (transvectionUnit (Sum.inl j : Index (r + 1)) (Sum.inr j) (by intro h; cases h) b) := by
  apply commute_transvection_of_zero_products (initialShortRoot K r a).val
    (initialShortMatrix K r hr) a (initialShortRoot_coe K r hr a)
  · simp [initialShortMatrix, sub_mul, hj, Ne.symm hj]
  · simp [initialShortMatrix, mul_sub, hj, Ne.symm hj]

theorem initialShort_commutes_lower_zero (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (a b : K) :
    Commute (initialShortRoot K r a).val
      (transvectionUnit (Sum.inr (0 : Fin (r + 1)) : Index (r + 1)) (Sum.inl 0)
        (by intro h; cases h) b) := by
  have h01 : (0 : Fin (r + 1)) ≠ (⟨1, Nat.succ_lt_succ hr⟩ : Fin (r + 1)) := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = 1 at hv
    omega
  apply commute_transvection_of_zero_products (initialShortRoot K r a).val
    (initialShortMatrix K r hr) a (initialShortRoot_coe K r hr a)
  · simp [initialShortMatrix, sub_mul, h01, Ne.symm h01]
  · simp [initialShortMatrix, mul_sub, h01, Ne.symm h01]

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
