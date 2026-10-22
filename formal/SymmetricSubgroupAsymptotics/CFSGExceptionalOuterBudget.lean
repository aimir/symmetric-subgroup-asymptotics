import SymmetricSubgroupAsymptotics.CFSGExceptionalOriginalOuterBound
import SymmetricSubgroupAsymptotics.CFSGExceptionalRootDegree
import SymmetricSubgroupAsymptotics.CFSGE6SmallIndexField
import SymmetricSubgroupAsymptotics.CFSGFieldTwoScaling
import SymmetricSubgroupAsymptotics.CFSGSufficientSimpleIndexBounds

/-! Actual sufficient outer-order budgets for original E6/E7/E8.
The E6 small-index branch uses its proved two-element-field reduction;
all remaining constants come from the actual field and Cartan factors. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalOuterBudget
open CFSG.Models.Chevalley PrimitiveSocleRawStructure
open CFSGExceptionalOriginalOuterBound CFSGExceptionalRootDegree
open CFSGFiniteFieldAutomorphisms CFSGE6SmallIndexField CFSGFieldTwoScaling

private theorem fieldAut_le_four (K : Type) [Field K] [Finite K] (hK : Nat.card K < 30) :
    Nat.card (K ≃+* K) ≤ 4 := by
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨_,hp,_⟩ := FiniteField.card K (ringChar K)
  letI : Fact (ringChar K).Prime := ⟨hp⟩
  letI : Algebra (ZMod (ringChar K)) K := ZMod.algebra K (ringChar K)
  have hpow : 2 ^ Nat.card (K ≃+* K) ≤ Nat.card K :=
    (Nat.pow_le_pow_left hp.two_le _).trans_eq (field_card_eq_pow_card_ringAut K (ringChar K))
  by_contra hne
  have hfive : 5 ≤ Nat.card (K ≃+* K) := by omega
  have h32 : 32 ≤ 2 ^ Nat.card (K ≃+* K) := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hfive
  omega

private theorem field_log_le_index (K : Type) [Field K] [Finite K] (ell : ℕ)
    (hK : Nat.card K ≤ ell) : Real.logb 2 (Nat.card K) ≤ Real.logb 2 ell :=
  Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast (Nat.card_pos (α := K)))
    (by exact_mod_cast hK)

private theorem budget_of_raw_six (K : Type) [Field K] [Finite K] (ell out : ℕ)
    (hK : Nat.card K ≤ ell) (hout : out ≤ 6 * Nat.card (K ≃+* K))
    (hsmall : ell < 27 → (out : ℝ) ≤ 3 * Real.logb 2 ell) : SufficientOuterOrderBudget ell out := by
  have hf := (card_ringAut_le_logb K).trans (field_log_le_index K ell hK)
  have hreal : (out : ℝ) ≤ 6 * (Nat.card (K ≃+* K) : ℝ) := by exact_mod_cast hout
  refine ⟨by linarith, hsmall, ?_⟩
  intro he
  have hfour := fieldAut_le_four K (hK.trans_lt he)
  omega

private theorem budget_of_raw_two (K : Type) [Field K] [Finite K] (ell out : ℕ)
    (hK : Nat.card K ≤ ell) (hout : out ≤ 2 * Nat.card (K ≃+* K)) :
    SufficientOuterOrderBudget ell out := by
  apply budget_of_raw_six K ell out hK
    (hout.trans (Nat.mul_le_mul_right _ (by decide : 2 ≤ 6)))
  intro _
  have hf := (card_ringAut_le_logb K).trans (field_log_le_index K ell hK)
  have hreal : (out : ℝ) ≤ 2 * (Nat.card (K ≃+* K) : ℝ) := by exact_mod_cast hout
  have hnonneg : 0 ≤ Real.logb 2 (ell : ℝ) :=
    Real.logb_nonneg (by norm_num) (by
      exact_mod_cast ((Finite.one_lt_card (α := K)).le.trans hK))
  linarith

theorem serreTypeE6_sufficient_outer_budget (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₆ K)]
    (ell : ℕ) (hell : LeastProperIndex (Projective CartanMatrix.E₆ K) ell) :
    SufficientOuterOrderBudget ell (Nat.card (Outer (Projective CartanMatrix.E₆ K))) := by
  obtain ⟨H,hH,hi⟩ := hell.1
  have hK : Nat.card K ≤ ell := hi ▸ serreTypeE6_field_card_le_index K p H hH
  apply budget_of_raw_six K ell _ hK (serreTypeE6_outer_card_le K p)
  intro hsmall
  have htwo := field_card_eq_two_of_index_lt_twentySeven K p ell hell hsmall
  have hout : Nat.card (Outer (Projective CartanMatrix.E₆ K)) ≤ 2 := by
    calc
      _ ≤ ((CFSGIntegerMatrixPowerHom.powerHom (G := Kˣ) CartanMatrix.E₆).range.index *
          Nat.card (K ≃+* K)) * 2 := serreTypeE6_outer_card_le_cartan K p
      _ ≤ (1 * 1) * 2 := Nat.mul_le_mul_right 2
        (Nat.mul_le_mul (scaling_index_le_one K CartanMatrix.E₆ htwo) (fieldAut_card_le_one K htwo))
      _ = 2 := by decide
  have houtR : (Nat.card (Outer (Projective CartanMatrix.E₆ K)) : ℝ) ≤ 2 := by exact_mod_cast hout
  have hlog : 1 ≤ Real.logb 2 (ell : ℝ) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)
      (by exact_mod_cast (htwo ▸ hK) : (2 : ℝ) ≤ ell)
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using hh
  linarith

theorem serreTypeE7_sufficient_outer_budget (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₇ K)]
    (ell : ℕ) (hell : LeastProperIndex (Projective CartanMatrix.E₇ K) ell) :
    SufficientOuterOrderBudget ell (Nat.card (Outer (Projective CartanMatrix.E₇ K))) := by
  obtain ⟨H,hH,hi⟩ := hell.1
  exact budget_of_raw_two K ell _ (hi ▸ serreTypeE7_field_card_le_index K p H hH)
    (serreTypeE7_outer_card_le K p)

theorem serreTypeE8_sufficient_outer_budget (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₈ K)]
    (ell : ℕ) (hell : LeastProperIndex (Projective CartanMatrix.E₈ K) ell) :
    SufficientOuterOrderBudget ell (Nat.card (Outer (Projective CartanMatrix.E₈ K))) := by
  obtain ⟨H,hH,hi⟩ := hell.1
  apply budget_of_raw_two K ell _ (hi ▸ serreTypeE8_field_card_le_index K p H hH)
  exact (serreTypeE8_outer_card_le K p).trans (Nat.mul_le_mul_right _ (by decide : 1 ≤ 2))

end SymmetricSubgroupAsymptotics.CFSGExceptionalOuterBudget
