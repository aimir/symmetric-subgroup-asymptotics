import SymmetricSubgroupAsymptotics.TernaryFullFactorSmall
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Unconditional ternary full-subspace growth

Actual rank-d subspaces are counted by their actual ordered bases. A
simple lower bound for each basis factor suffices for the sharp quadratic
coefficient in the full-coordinate weighted sum. No ternary Euler-product
input, supplied Gaussian count, or physical marker-collapse premise is used.
The final repeat bound keeps L3(1)=1 exactly; only the linear error is loose.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.TernarySubspaceEnvelope

open TernaryFullWeightReindex DiagonalFullSubmoduleWeights DiagonalFullSubmoduleEquiv
open DiagonalInvariantSubmodules

abbrev Space (a : ℕ) := Fin a → ZMod 3
abbrev RankSubspace (a d : ℕ) :=
  {S : Submodule (ZMod 3) (Space a) // Module.finrank (ZMod 3) S=d}

private instance submoduleFinite (a : ℕ) : Finite (Submodule (ZMod 3) (Space a)) :=
  Finite.of_injective (fun S : Submodule (ZMod 3) (Space a) => (S : Set (Space a)))
    SetLike.coe_injective

private instance fullSubmoduleFinite (a : ℕ) :
    Finite (FullSubmodule (k := ZMod 3) (Fin a)) :=
  Finite.of_injective (fun S : FullSubmodule (k := ZMod 3) (Fin a) => S.val)
    Subtype.val_injective

private abbrev Frame (a d : ℕ) :=
  {v : Fin d → Space a // LinearIndependent (ZMod 3) v}

private def frameSpan {a d : ℕ} (v : Frame a d) : Submodule (ZMod 3) (Space a) :=
  Submodule.span (ZMod 3) (Set.range v.1)

private theorem frameSpan_finrank {a d : ℕ} (v : Frame a d) :
    Module.finrank (ZMod 3) (frameSpan v)=d := by
  simpa [frameSpan] using finrank_span_eq_card v.2

private theorem span_inside_eq {a d : ℕ}
    (S : Submodule (ZMod 3) (Space a)) (hS : Module.finrank (ZMod 3) S=d)
    (v : Fin d → S) (hv : LinearIndependent (ZMod 3) v) :
    Submodule.span (ZMod 3) (Set.range (fun i => (v i : Space a)))=S := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact (v i).2
  · have hrank := finrank_span_eq_card (hv.map' S.subtype (by simp))
    simpa [Function.comp_def,hS] using hrank

private def frameSpanFibreEquiv {a d : ℕ}
    (S : Submodule (ZMod 3) (Space a)) (hS : Module.finrank (ZMod 3) S=d) :
    {v : Frame a d // frameSpan v=S} ≃
      {v : Fin d → S // LinearIndependent (ZMod 3) v} where
  toFun v := ⟨fun i => ⟨v.1.1 i,
    v.2.le (Submodule.subset_span (Set.mem_range_self i))⟩,
    LinearIndependent.of_comp S.subtype v.1.2⟩
  invFun v := ⟨⟨fun i => (v.1 i : Space a),v.2.map' S.subtype (by simp)⟩,
    span_inside_eq S hS v.1 v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Fraction-free counting identity for all actual rank-d ternary subspaces. -/
theorem rank_count_mul (a d : ℕ) (hd : d≤a) :
    Nat.card (RankSubspace a d) * (∏ i : Fin d, (3^d-3^i.val)) =
      ∏ i : Fin d, (3^a-3^i.val) := by
  let e := Equiv.sigmaSubtypeFiberEquiv (frameSpan (a := a) (d := d))
    (fun S => Module.finrank (ZMod 3) S=d) frameSpan_finrank
  have h := Nat.card_congr e
  rw [Nat.card_sigma] at h
  have hf (S : RankSubspace a d) :
      Nat.card {v : Frame a d // frameSpan v=S.1}=
        ∏ i : Fin d, (3^d-3^i.val) := by
    rw [Nat.card_congr (frameSpanFibreEquiv S.1 S.2),card_linearIndependent]
    · simp [S.2]
    · omega
  simp only [hf,Finset.sum_const,Finset.card_univ,smul_eq_mul,
    ← Nat.card_eq_fintype_card] at h
  rw [h]
  simpa using card_linearIndependent (K := ZMod 3) (V := Space a)
    (k := d) (by simpa using hd)

private theorem basis_factor_lower (d : ℕ) (i : Fin d) :
    3^(d-1)≤3^d-3^i.val := by
  have hi : i.val≤d-1 := by omega
  have hp : (3:ℕ)^i.val≤3^(d-1) := Nat.pow_le_pow_right (by decide) hi
  have hd : d-1+1=d := by omega
  have he : (3:ℕ)^d=3^(d-1)*3 := by
    calc
      (3:ℕ)^d=3^((d-1)+1) := congrArg (fun j => (3:ℕ)^j) hd.symm
      _ = _ := pow_succ _ _
  rw [he]
  omega

/-- A uniform rank-count estimate with the correct quadratic coefficient.
The extra linear d in the exponent avoids any Euler-product hypothesis. -/
theorem rank_count_le (a d : ℕ) (hd : d≤a) :
    Nat.card (RankSubspace a d)≤3^(d*(a-d+1)) := by
  have hden : (3:ℕ)^(d*(d-1))≤∏ i : Fin d, (3^d-3^i.val) := by
    calc
      _ = ∏ _i : Fin d, (3:ℕ)^(d-1) := by simp [← pow_mul,Nat.mul_comm]
      _ ≤ _ := Finset.prod_le_prod' (fun i _ => basis_factor_lower d i)
  have hnum : (∏ i : Fin d, (3^a-3^i.val))≤(3:ℕ)^(a*d) := by
    calc
      _ ≤ ∏ _i : Fin d, (3:ℕ)^a :=
        Finset.prod_le_prod' (fun i _ => Nat.sub_le _ _)
      _ = _ := by simp [← pow_mul]
  have hm : Nat.card (RankSubspace a d)*3^(d*(d-1))≤(3:ℕ)^(a*d) :=
    (Nat.mul_le_mul_left _ hden).trans ((rank_count_mul a d hd).le.trans hnum)
  have he : d*(a-d+1)+d*(d-1)=a*d := by
    by_cases hzero : d=0
    · simp [hzero]
    · have h1 : d-1+1=d := by omega
      have h2 : a-d+d=a := Nat.sub_add_cancel hd
      nlinarith
  have hp : (3:ℕ)^(d*(a-d+1))*3^(d*(d-1))=3^(a*d) := by rw [← pow_add,he]
  rw [← hp] at hm
  exact Nat.le_of_mul_le_mul_right hm (pow_pos (by decide) _)

private def rankIndex (a : ℕ) (S : Submodule (ZMod 3) (Space a)) : Fin (a+1) :=
  ⟨Module.finrank (ZMod 3) S,Nat.lt_succ_of_le (by simpa using S.finrank_le)⟩

/-- Partition the entire original subspace lattice by its actual dimension. -/
theorem weighted_subspace_sum_eq (a : ℕ) :
    (∑ S : Submodule (ZMod 3) (Space a), 3^(a-Module.finrank (ZMod 3) S))=
      ∑ d : Fin (a+1), Nat.card (RankSubspace a d.val)*3^(a-d.val) := by
  have h := (Equiv.sigmaFiberEquiv (rankIndex a)).sum_comp
    (fun S : Submodule (ZMod 3) (Space a) => (3:ℕ)^(a-Module.finrank (ZMod 3) S))
  rw [Fintype.sum_sigma] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro d _
  change (∑ S : {S : Submodule (ZMod 3) (Space a) // rankIndex a S=d},
      (3:ℕ)^(a-Module.finrank (ZMod 3) S.val)) =
    Nat.card (RankSubspace a d.val)*3^(a-d.val)
  have hr (S : {S : Submodule (ZMod 3) (Space a) // rankIndex a S=d}) :
      Module.finrank (ZMod 3) S.val=d.val := congrArg Fin.val S.property
  simp_rw [hr]
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  congr 1
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun _ => Fin.ext_iff)

/-- Forgetting the full-coordinate condition only enlarges the actual sum. -/
theorem full_factor_le_all_subspaces (a : ℕ) :
    ternaryFullFactor a≤
      ∑ S : Submodule (ZMod 3) (Space a), 3^(a-Module.finrank (ZMod 3) S) := by
  unfold ternaryFullFactor ternaryFullWeight
  rw [Fintype.card_fin]
  let e : FullSubmodule (k := ZMod 3) (Fin a) ↪ Submodule (ZMod 3) (Space a) :=
    ⟨Subtype.val,Subtype.val_injective⟩
  calc
    _ = ∑ S ∈ Finset.univ.map e, (3:ℕ)^(a-Module.finrank (ZMod 3) S) := by
      rw [Finset.sum_map]
      rfl
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => Nat.zero_le _)

private theorem weighted_rank_le (a d : ℕ) (hd : d≤a) :
    (Nat.card (RankSubspace a d) : ℝ)*(3:ℝ)^(a-d)≤
      (3:ℝ)^((a:ℝ)^2/4+a) := by
  have hc : (Nat.card (RankSubspace a d) : ℝ)≤(3:ℝ)^(d*(a-d+1)) := by
    exact_mod_cast rank_count_le a d hd
  calc
    _ ≤ (3:ℝ)^(d*(a-d+1))*(3:ℝ)^(a-d) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (3:ℝ)^(d*(a-d+1)+(a-d)) := (pow_add _ _ _).symm
    _ ≤ _ := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast [Nat.cast_sub hd]
      nlinarith [sq_nonneg ((a:ℝ)-2*d)]

/-- A complete unconditional envelope for the literal ternary full-subspace
factor, including a=0. Its leading quadratic coefficient is one quarter. -/
theorem full_factor_le_quadratic (a : ℕ) :
    (ternaryFullFactor a : ℝ)≤((a:ℝ)+1)*(3:ℝ)^((a:ℝ)^2/4+a) := by
  have hf : (ternaryFullFactor a : ℝ)≤
      ((∑ d : Fin (a+1), Nat.card (RankSubspace a d.val)*3^(a-d.val) : ℕ) : ℝ) := by
    exact_mod_cast (full_factor_le_all_subspaces a).trans_eq (weighted_subspace_sum_eq a)
  calc
    _ ≤ _ := hf
    _ = ∑ d : Fin (a+1),
        (Nat.card (RankSubspace a d.val) : ℝ)*(3:ℝ)^(a-d.val) := by push_cast; rfl
    _ ≤ ∑ _d : Fin (a+1), (3:ℝ)^((a:ℝ)^2/4+a) :=
      Finset.sum_le_sum (fun d _ => weighted_rank_le a d.val (by omega))
    _ = _ := by simp [Finset.sum_const,nsmul_eq_mul]

private theorem add_one_le_three_pow_pred (a : ℕ) (ha : 2≤a) :
    a+1≤(3:ℕ)^(a-1) := by
  induction a, ha using Nat.le_induction with
  | base => norm_num
  | succ a ha ih =>
    have he : a+1-1=(a-1)+1 := by omega
    rw [he,pow_succ]
    nlinarith

/-- Per-repeat form for positive marker multiplicities. The singleton
factor is exactly one, and every nonconstant contribution is charged to
repeated occurrences. The leading quadratic coefficient is unchanged. -/
theorem full_factor_le_repeat (a : ℕ) (ha : 1≤a) :
    (ternaryFullFactor a : ℝ)≤
      (3:ℝ)^(((a:ℝ)-1)^2/4+15*((a:ℝ)-1)/4) := by
  by_cases h1 : a=1
  · subst a
    simp [TernaryFullFactorSmall.factor_one]
  have haNat : 2≤a := by omega
  have haReal : (2:ℝ)≤a := by exact_mod_cast haNat
  have haPow : (a:ℝ)+1≤(3:ℝ)^((a:ℝ)-1) := by
    have h := add_one_le_three_pow_pred a haNat
    have hcast : (a:ℝ)+1≤(3:ℝ)^(a-1) := by exact_mod_cast h
    rw [← Real.rpow_natCast, Nat.cast_sub ha] at hcast
    norm_num at hcast ⊢
    exact hcast
  calc
    _ ≤ ((a:ℝ)+1)*(3:ℝ)^((a:ℝ)^2/4+a) := full_factor_le_quadratic a
    _ ≤ (3:ℝ)^((a:ℝ)-1)*(3:ℝ)^((a:ℝ)^2/4+a) :=
      mul_le_mul_of_nonneg_right haPow (by positivity)
    _ = (3:ℝ)^(((a:ℝ)-1)+((a:ℝ)^2/4+a)) :=
      (Real.rpow_add (by norm_num) _ _).symm
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith

/-- Products over any actual finite distinct-label type depend on the
number of repeats, not on the number of singleton sign classes. -/
theorem full_factor_product_le {Q : Type*} [Fintype Q]
    (a : Q → ℕ) (ha : ∀ q, 1≤a q) :
    (∏ q, (ternaryFullFactor (a q) : ℝ))≤
      (3:ℝ)^((((∑ q, (a q-1) : ℕ) : ℝ)^2)/4+
        15*((∑ q, (a q-1) : ℕ) : ℝ)/4) := by
  have hs : (∑ q, ((a q:ℝ)-1))=((∑ q, (a q-1) : ℕ) : ℝ) := by
    calc
      _ = ∑ q, ((a q-1:ℕ):ℝ) := by
        apply Finset.sum_congr rfl
        intro q _
        rw [Nat.cast_sub (ha q),Nat.cast_one]
      _ = _ := (Nat.cast_sum Finset.univ (fun q => a q-1)).symm
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun q => (a q:ℝ)-1)
    (fun q _ => sub_nonneg.mpr (by exact_mod_cast ha q))
  rw [hs] at hsq
  calc
    _ ≤ ∏ q, (3:ℝ)^(((a q:ℝ)-1)^2/4+15*((a q:ℝ)-1)/4) := by
      apply Finset.prod_le_prod
      · intro q _
        exact Nat.cast_nonneg _
      · intro q _
        exact full_factor_le_repeat (a q) (ha q)
    _ = (3:ℝ)^(∑ q, (((a q:ℝ)-1)^2/4+15*((a q:ℝ)-1)/4)) :=
      (Real.rpow_sum_of_pos (by norm_num) _ _).symm
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      rw [Finset.sum_add_distrib,← Finset.sum_div,← Finset.sum_div,
        ← Finset.mul_sum,hs]
      linarith

end SymmetricSubgroupAsymptotics.TernarySubspaceEnvelope
