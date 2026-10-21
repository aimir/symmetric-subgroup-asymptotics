import SymmetricSubgroupAsymptotics.CFSGOrdinarySubgroupUpperReduction
import SymmetricSubgroupAsymptotics.ElementaryDixonOrderWithoutCatalogue
import SymmetricSubgroupAsymptotics.MarkedC4OrdinarySubgroupUpper

/-! Quantitative ordinary core costs. The exponentially bounded ACTUAL
soluble container, rather than the whole symmetric group, is the tuple
alphabet. Consequently the bounded-orbit nilpotent-core step has O_C(n√n)
cost, without an extra logarithm. No nilpotent counting estimate is assumed
proved by this numerical calculation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrdinarySubgroupUpperReduction
open MarkedC4

/-- A full actual-container tuple costs at most 4*K*n*sqrt(n) in base two. -/
theorem container_tuple_power_le (K b : ℕ) :
    (((2^(2*b))^(K*Nat.sqrt (2*b)) : ℕ) : ℝ) ≤
      (2 : ℝ)^(4*(K : ℝ)*b*Real.sqrt b) := by
  have hb0 : (0 : ℝ)≤b := Nat.cast_nonneg b
  have hs : (Nat.sqrt (2*b) : ℝ)≤2*Real.sqrt b := by
    have hs0 : (0 : ℝ)≤Nat.sqrt (2*b) := Nat.cast_nonneg _
    have hn : (Nat.sqrt (2*b) : ℝ)^2≤2*(b : ℝ) := by
      rw [pow_two]
      exact_mod_cast Nat.sqrt_le (2*b)
    have hr := Real.sq_sqrt hb0
    have hrs := Real.sqrt_nonneg (b : ℝ)
    nlinarith
  rw [←pow_mul,Nat.cast_pow,Nat.cast_ofNat,←Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  push_cast
  have hm := mul_le_mul_of_nonneg_left hs (show 0≤2*(b : ℝ)*(K : ℝ) by positivity)
  nlinarith

/-- Dixon is already proved in the project. Thus the ordinary bounded
soluble-to-nilpotent count needs no retained order-theorem premise. -/
theorem bounded_soluble_real_card_le (C b : ℕ) :
    (Nat.card (OrbitCutoffFamilies.SolubleFamily C b) : ℝ) ≤
      (Nat.card (SolubleContainerCount.Index (Fin b)) : ℝ) *
        (Nat.card (NilpotentSources b) : ℝ) *
          (2 : ℝ)^(4*(OrdinaryNilpotentGeneration.nilpotentControlCutoff C : ℝ)*b*Real.sqrt b) := by
  have h := bounded_soluble_card_le_menu_mul_nilpotent
    ElementaryDixonOrderProof.WithoutCatalogue.dixonOrder_of_primitive_inputs C b
  calc
    _ ≤ (Nat.card (SolubleContainerCount.Index (Fin b)) : ℝ) *
        (Nat.card (NilpotentSources b) : ℝ) *
          (((2^(2*b))^(OrdinaryNilpotentGeneration.nilpotentControlCutoff C*Nat.sqrt (2*b)) : ℕ) : ℝ) := by
      exact_mod_cast h
    _ ≤ _ := mul_le_mul_of_nonneg_left (container_tuple_power_le _ _) (by positivity)

/-- The final one-generator step preserves the sharp quadratic term.
Its only multiplicity is the actual symmetric-group order n!. -/
theorem ordinary_upper_at_degree_of_soluble_estimate
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (n : ℕ) (B E : ℝ)
    (hsol : (Nat.card {J : Subgroup (PermutationGroup n) // IsSolvable J} : ℝ) ≤
      (2 : ℝ)^((n : ℝ)^2/16+B*n*Real.sqrt n))
    (hfac : (n.factorial : ℝ)≤(2 : ℝ)^(E*n*Real.sqrt n)) :
    (Nat.card (Subgroup (PermutationGroup n)) : ℝ) ≤
      (2 : ℝ)^((n : ℝ)^2/16+(B+E)*n*Real.sqrt n) := by
  have hc := subgroup_card_le_card_mul_soluble hAG (PermutationGroup n)
  have horder : Nat.card (PermutationGroup n)=n.factorial := by
    simp only [PermutationGroup,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
  rw [horder] at hc
  calc
    _ ≤ (n.factorial : ℝ)*(Nat.card {J : Subgroup (PermutationGroup n) // IsSolvable J} : ℝ) := by
      exact_mod_cast hc
    _ ≤ (2 : ℝ)^(E*n*Real.sqrt n) *
        (2 : ℝ)^((n : ℝ)^2/16+B*n*Real.sqrt n) :=
      mul_le_mul hfac hsol (by positivity) (by positivity)
    _ = _ := by
      rw [←Real.rpow_add (by norm_num : (0 : ℝ)<2)]
      congr 1
      ring

end SymmetricSubgroupAsymptotics.CFSGOrdinarySubgroupUpperReduction
