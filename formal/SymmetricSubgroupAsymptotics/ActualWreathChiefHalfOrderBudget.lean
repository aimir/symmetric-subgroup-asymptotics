import SymmetricSubgroupAsymptotics.ActualWreathOrdinaryChiefRecurrence
import SymmetricSubgroupAsymptotics.ActualWreathChiefFactorOrder
import Mathlib.FieldTheory.Finiteness

/-! An actual finite chief-cost aggregate, with no ceiling accumulated
at individual layers. The proved half-capacity and genuine local factor
orders give 2^(2*cost) <= |local D|^(number of blocks). This is a coarse
baseline, not the sharp permutation Tracey bound. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathChiefHalfOrderBudget
open PermutationalWreathProduct

theorem card_kernel_mul_card_of_surjective
    {D D' : Type} [Group D] [Finite D] [Group D'] [Finite D']
    (phi : D →* D') (hphi : Function.Surjective phi) :
    Nat.card phi.ker * Nat.card D' = Nat.card D := by
  have hi : phi.ker.index = Nat.card D' := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hphi, Subgroup.card_top]
  simpa only [hi] using phi.ker.card_mul_index

theorem elementary_kernel_card
    {D D' : Type} [Group D] [Group D']
    (phi : D →* D') (C : ElementaryMinimalNormalChart phi.ker) :
    Nat.card phi.ker = C.p ^ Module.finrank (ZMod C.p) C.V := by
  letI : Finite C.V := Module.finite_of_finite (ZMod C.p)
  calc
    Nat.card phi.ker = Nat.card (Multiplicative C.V) := Nat.card_congr C.equiv.toEquiv
    _ = Nat.card C.V := Nat.card_congr Multiplicative.toAdd
    _ = C.p ^ Module.finrank (ZMod C.p) C.V := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod C.p), Nat.card_zmod]

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]

theorem elementary_cost_pow_le (S : ActualWreathCompressionState Q I)
    {D' : Type} [Group D'] [Finite D']
    (phi : S.D →* D') (C : ElementaryMinimalNormalChart phi.ker)
    (i : I) (hI : 2 ≤ Fintype.card I) :
    2 ^ (2 * ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i) ≤
      Nat.card phi.ker ^ Fintype.card I := by
  have hhalf := ActualWreathElementaryOrdinaryStep.layerCapacity_le_half S phi C i hI
  have hn : 2 * ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i ≤
      Module.finrank (ZMod C.p) C.V * Fintype.card I := by
    have hh := (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hhalf
    have hhN : ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i * 2 ≤
        Module.finrank (ZMod C.p) C.V * Fintype.card I := by
      exact_mod_cast hh
    exact (Nat.mul_comm 2 _).le.trans hhN
  calc
    2 ^ (2 * ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i) ≤
        2 ^ (Module.finrank (ZMod C.p) C.V * Fintype.card I) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) hn
    _ = (2 ^ Module.finrank (ZMod C.p) C.V) ^ Fintype.card I := pow_mul _ _ _
    _ ≤ (C.p ^ Module.finrank (ZMod C.p) C.V) ^ Fintype.card I :=
      Nat.pow_le_pow_left (Nat.pow_le_pow_left C.p_prime.two_le _) _
    _ = Nat.card phi.ker ^ Fintype.card I := by rw [elementary_kernel_card phi C]

theorem cost_two_pow_le_local_order_pow
    {i : I} {S : ActualWreathCompressionState Q I} {n : ℕ}
    (h : ActualWreathOrdinaryChiefRecurrence.ChiefCost i S n)
    (hI : 2 ≤ Fintype.card I) :
    2 ^ (2 * n) ≤ Nat.card S.D ^ Fintype.card I := by
  induction h with
  | terminal S hD =>
      simp only [Nat.mul_zero, pow_zero]
      exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (Nat.card_pos (α := S.D)).ne')
  | vanishing S D' phi hphi hmin hz n next ih =>
      exact ih.trans (Nat.pow_le_pow_left (Nat.card_le_card_of_surjective phi hphi) _)
  | elementary S D' phi hphi hmin C n next ih =>
      calc
        2 ^ (2 * (ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i + n)) =
            2 ^ (2 * ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i) *
              2 ^ (2 * n) := by rw [Nat.mul_add, pow_add]
        _ ≤ Nat.card phi.ker ^ Fintype.card I * Nat.card D' ^ Fintype.card I :=
          Nat.mul_le_mul (elementary_cost_pow_le S phi C i hI) ih
        _ = Nat.card S.D ^ Fintype.card I := by
          rw [← mul_pow, card_kernel_mul_card_of_surjective phi hphi]
  | nonabelian S D' phi hphi hmin hnc hne C j n next ih =>
      have hf := ActualWreathChiefFactorOrder.two_pow_factor_genRank_le_local_kernel
        S.rho phi S.rho_injective C j
      have he : 2 ^ (2 * MarkedC4.genRank (C.factor j)) ≤
          Nat.card phi.ker ^ Fintype.card I := by
        calc
          2 ^ (2 * MarkedC4.genRank (C.factor j)) =
              (2 ^ MarkedC4.genRank (C.factor j)) ^ 2 := by
            rw [Nat.mul_comm 2 (MarkedC4.genRank (C.factor j)), pow_mul]
          _ ≤ Nat.card phi.ker ^ 2 := Nat.pow_le_pow_left hf _
          _ ≤ Nat.card phi.ker ^ Fintype.card I :=
            Nat.pow_le_pow_right (Nat.card_pos (α := phi.ker)) hI
      calc
        2 ^ (2 * (MarkedC4.genRank (C.factor j) + n)) =
            2 ^ (2 * MarkedC4.genRank (C.factor j)) * 2 ^ (2 * n) := by
          rw [Nat.mul_add, pow_add]
        _ ≤ Nat.card phi.ker ^ Fintype.card I * Nat.card D' ^ Fintype.card I :=
          Nat.mul_le_mul he ih
        _ = Nat.card S.D ^ Fintype.card I := by
          rw [← mul_pow, card_kernel_mul_card_of_surjective phi hphi]

theorem source_genRank_two_pow_le (S : ActualWreathCompressionState Q I)
    (i : I) (hI : 2 ≤ Fintype.card I) :
    2 ^ (2 * MarkedC4.genRank S.A) ≤
      Nat.card S.D ^ Fintype.card I * 2 ^ (2 * MarkedC4.genRank Q) := by
  obtain ⟨n, hn⟩ := ActualWreathOrdinaryChiefRecurrence.exists_chiefCost i S
  have hg := ActualWreathOrdinaryChiefRecurrence.genRank_le_cost_add_top hn
  calc
    2 ^ (2 * MarkedC4.genRank S.A) ≤ 2 ^ (2 * (n + MarkedC4.genRank Q)) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.mul_le_mul_left 2 hg)
    _ = 2 ^ (2 * n) * 2 ^ (2 * MarkedC4.genRank Q) := by rw [Nat.mul_add, pow_add]
    _ ≤ Nat.card S.D ^ Fintype.card I * 2 ^ (2 * MarkedC4.genRank Q) :=
      Nat.mul_le_mul_right _ (cost_two_pow_le_local_order_pow hn hI)

end SymmetricSubgroupAsymptotics.ActualWreathChiefHalfOrderBudget
