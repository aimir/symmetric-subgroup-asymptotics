import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitarySubspaceAction
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRankOneGeneration

/-! The two genuine small bases for recursive isotropic-space
normalization. Rank zero is anisotropic. In rank one the isotropic
coordinate ratio belongs to the literal Frobenius-fixed field, so an
actual fixed root followed by the actual signed reversal clears it.
Neither a named SU2 identification nor a transitivity premise is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryParameters CFSGSerreOrdinaryTwists
open CFSGSerreSquareZeroMatrix

theorem rank_zero_isotropic_eq_zero (q : CFSG.PrimePower)
    (x : Fin 1 → q.Extension 2) (hx : unitaryNaturalPair q 0 x x = 0) : x = 0 := by
  have hJ : (signedReversalUnit (q.Extension 2) 0 : Mat (q.Extension 2) 0) = 1 := by
    ext i j
    rw [Fin.eq_zero i, Fin.eq_zero j]
    simp [signedReversalUnit_apply, signWeight]
  change hermitianPair (definingFieldAutomorphism q 2) _ x x = 0 at hx
  rw [hJ] at hx
  have hc : definingFieldAutomorphism q 2 (x 0) * x 0 = 0 := by
    simpa [hermitianPair, Matrix.one_mulVec, dotProduct, Fin.sum_univ_one] using hx
  have hz : x 0 = 0 := by
    rcases mul_eq_zero.mp hc with h | h
    · exact (map_eq_zero (definingFieldAutomorphism q 2)).mp h
    · exact h
  ext i
  rw [Fin.eq_zero i]
  exact hz

theorem rank_zero_pair_zero_subspace (q : CFSG.PrimePower)
    (S : Submodule (q.Extension 2) (Fin 1 → q.Extension 2))
    (hS : ∀ x ∈ S, ∀ y ∈ S, unitaryNaturalPair q 0 x y = 0) : S = ⊥ := by
  apply le_antisymm
  · intro x hx
    exact (Submodule.mem_bot (q.Extension 2)).mpr (rank_zero_isotropic_eq_zero q x (hS x hx x hx))
  · exact bot_le

theorem rank_one_pair_formula (q : CFSG.PrimePower) (x y : Fin 2 → q.Extension 2) :
    unitaryNaturalPair q 1 x y =
      definingFieldAutomorphism q 2 (x 0) * y 1 -
        definingFieldAutomorphism q 2 (x 1) * y 0 := by
  change hermitianPair _ _ x y = _
  rw [signedReversal_rank_one]
  simp [hermitianPair, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    sub_eq_add_neg, mul_add]

theorem rank_one_isotropic_ratio_fixed (q : CFSG.PrimePower)
    (x : Fin 2 → q.Extension 2) (hx : unitaryNaturalPair q 1 x x = 0)
    (hb : x 1 ≠ 0) :
    definingFieldAutomorphism q 2 (x 0 / x 1) = x 0 / x 1 := by
  rw [rank_one_pair_formula] at hx
  rw [map_div₀]
  apply (div_eq_div_iff ((map_ne_zero (definingFieldAutomorphism q 2)).mpr hb) hb).mpr
  exact (sub_eq_zero.mp hx).trans (mul_comm _ _)

theorem exists_rank_one_isotropic_vector_axis (q : CFSG.PrimePower)
    (x : Fin 2 → q.Extension 2) (hx : x ≠ 0)
    (hiso : unitaryNaturalPair q 1 x x = 0) :
    ∃ (g : naturalFixed 1 q) (a : q.Extension 2), a ≠ 0 ∧
      unitaryNaturalLinearEquiv q 1 g x = a • Pi.single (0 : Fin 2) 1 := by
  by_cases hb : x 1 = 0
  · have ha : x 0 ≠ 0 := by
      intro h0
      apply hx
      ext i
      fin_cases i <;> simp [h0, hb]
    refine ⟨1, x 0, ha, ?_⟩
    change (1 : Mat (q.Extension 2) 1) *ᵥ x = _
    rw [Matrix.one_mulVec]
    ext i
    fin_cases i <;> simp [Pi.single_apply, hb]
  · have hratio := rank_one_isotropic_ratio_fixed q x hiso hb
    let t : rankOneFixedField q := ⟨-(x 0 / x 1), by
      change definingFieldAutomorphism q 2 (-(x 0 / x 1)) = -(x 0 / x 1)
      rw [map_neg, hratio]⟩
    let U : naturalFixed 1 q :=
      ⟨elementaryRoot (q.Extension 2) (naturalRootUnit (q.Extension 2) 1) false 0 t.val,
        rankOneRoot_fixed q false t⟩
    have hu : (U.val.val : Mat (q.Extension 2) 1) *ᵥ x =
        Pi.single (1 : Fin 2) (x 1) := by
      have hs : (Fin.succ (0 : Fin 1) : Fin 2) = 1 := rfl
      change ((1 : Mat (q.Extension 2) 1) + t.val • positive (q.Extension 2) 1 0) *ᵥ x = _
      ext i
      fin_cases i
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, positive, hs,
          Matrix.single_apply, Fin.castSucc_zero, t, hb]
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, positive, hs,
          Matrix.single_apply, Fin.castSucc_zero]
    refine ⟨reversalFixed q 1 * U, x 1, hb, ?_⟩
    change ((signedReversalUnit (q.Extension 2) 1 : Mat (q.Extension 2) 1) *
      (U.val.val : Mat (q.Extension 2) 1)) *ᵥ x = _
    rw [← Matrix.mulVec_mulVec, hu, signedReversal_rank_one]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
