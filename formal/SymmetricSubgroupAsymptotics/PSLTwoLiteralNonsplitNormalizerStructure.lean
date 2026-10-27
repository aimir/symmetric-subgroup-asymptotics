import SymmetricSubgroupAsymptotics.PSLTwoLiteralNonsplitTorusCyclic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Group
import Mathlib.Tactic.NormNum

/-!
Narrow adaptation of AxiomMath/CFSG69cb972f587a3ecc035e092253167ff2e303c962,
CharacterTheory/PSL2Table/Conjugacy.lean andBasic.lean (Apache-2.0).
Literal2x2 conjugation equations, with no classification/CFSG imports.
-/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.PSLTwoLiteralNonsplitNormalizerStructure
open PSLTwoLiteralNonsplitTorusCyclic
open Polynomial
variable {F : Type*} [Field F]
local notation "SL2" => Matrix.SpecialLinearGroup (Fin 2) F

theorem det_entries (A : SL2) : A.val 0 0*A.val 1 1-A.val 0 1*A.val 1 0=1 := by
  have h := A.property
  rw [Matrix.det_fin_two] at h
  exact h

theorem mul_apply_SL (A B : SL2) (i j : Fin 2) :
    (A*B).val i j=A.val i 0*B.val 0 j+A.val i 1*B.val 1 j := by
  rw [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]

theorem conj_apply_SL (M A : SL2) (i j : Fin 2) :
    (M*A*M⁻¹).val i j=
      (M.val i 0*A.val 0 0+M.val i 1*A.val 1 0)*(M⁻¹).val 0 j+
      (M.val i 0*A.val 0 1+M.val i 1*A.val 1 1)*(M⁻¹).val 1 j := by
  rw [mul_apply_SL,mul_apply_SL,mul_apply_SL]

theorem inv_apply_00 (M : SL2) : (M⁻¹).val 0 0=M.val 1 1 := by simp [Matrix.adjugate_fin_two]
theorem inv_apply_01 (M : SL2) : (M⁻¹).val 0 1= -M.val 0 1 := by simp [Matrix.adjugate_fin_two]
theorem inv_apply_10 (M : SL2) : (M⁻¹).val 1 0= -M.val 1 0 := by simp [Matrix.adjugate_fin_two]
theorem inv_apply_11 (M : SL2) : (M⁻¹).val 1 1=M.val 0 0 := by simp [Matrix.adjugate_fin_two]

theorem SL_ext {A B : SL2} (h00 : A.val 0 0=B.val 0 0) (h01 : A.val 0 1=B.val 0 1)
    (h10 : A.val 1 0=B.val 1 0) (h11 : A.val 1 1=B.val 1 1) : A=B := by
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

def IsAntiNS (ν : F) (M : SL2) : Prop :=
  M.val 1 1= -M.val 0 0 ∧ M.val 0 1= -(ν*M.val 1 0)

theorem mem_nonsplitSL_iff (ν : F) (A : SL2) :
    A ∈ nonsplitSL ν ↔ A.val 1 1=A.val 0 0 ∧ A.val 0 1=ν*A.val 1 0 := Iff.rfl
theorem conj_mem_nonsplitSL_iff (h2 : (2 : F) ≠ 0) {ν : F} (hν : ¬ IsSquare ν)
    {C : SL2} (hC : C ∈ nonsplitSL ν) (hy : (C : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0)
    (M : SL2) :
    M * C * M⁻¹ ∈ nonsplitSL ν ↔ M ∈ nonsplitSL ν ∨ IsAntiNS ν M := by
  obtain ⟨hC1, hC2⟩ := hC
  have hdet := det_entries M
  set α := (M : Matrix (Fin 2) (Fin 2) F) 0 0
  set β := (M : Matrix (Fin 2) (Fin 2) F) 0 1
  set γ := (M : Matrix (Fin 2) (Fin 2) F) 1 0
  set δ := (M : Matrix (Fin 2) (Fin 2) F) 1 1
  set x := (C : Matrix (Fin 2) (Fin 2) F) 0 0
  set y := (C : Matrix (Fin 2) (Fin 2) F) 1 0
  have e00 : ((M * C * M⁻¹ : SL2) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      x + y * (β * δ - ν * α * γ) := by
    rw [conj_apply_SL, inv_apply_00, inv_apply_10, hC1, hC2]
    linear_combination x * hdet
  have e11 : ((M * C * M⁻¹ : SL2) : Matrix (Fin 2) (Fin 2) F) 1 1 =
      x + y * (ν * α * γ - β * δ) := by
    rw [conj_apply_SL, inv_apply_01, inv_apply_11, hC1, hC2]
    linear_combination x * hdet
  have e01 : ((M * C * M⁻¹ : SL2) : Matrix (Fin 2) (Fin 2) F) 0 1 =
      y * (ν * α ^ 2 - β ^ 2) := by
    rw [conj_apply_SL, inv_apply_01, inv_apply_11, hC1, hC2]
    ring
  have e10 : ((M * C * M⁻¹ : SL2) : Matrix (Fin 2) (Fin 2) F) 1 0 =
      y * (δ ^ 2 - ν * γ ^ 2) := by
    rw [conj_apply_SL, inv_apply_00, inv_apply_10, hC1, hC2]
    ring
  rw [mem_nonsplitSL_iff, mem_nonsplitSL_iff, IsAntiNS, e00, e11, e01, e10]
  constructor
  · rintro ⟨h11, h01⟩
    have hI : ν * α * γ = β * δ := by
      have : y * (2 * (ν * α * γ - β * δ)) = 0 := by linear_combination h11
      rcases mul_eq_zero.mp this with h | h
      · exact (hy h).elim
      · rcases mul_eq_zero.mp h with h | h
        · exact (h2 h).elim
        · exact sub_eq_zero.mp h
    have hII : ν * α ^ 2 - β ^ 2 = ν * (δ ^ 2 - ν * γ ^ 2) := by
      have : y * ((ν * α ^ 2 - β ^ 2) - ν * (δ ^ 2 - ν * γ ^ 2)) = 0 := by
        linear_combination h01
      rcases mul_eq_zero.mp this with h | h
      · exact (hy h).elim
      · exact sub_eq_zero.mp h
    have hIII : (α - δ) * (β + ν * γ) = (α + δ) * (β - ν * γ) := by
      linear_combination 2 * hI
    have hIV : ν * ((α - δ) * (α + δ)) = (β - ν * γ) * (β + ν * γ) := by
      linear_combination hII
    by_cases hu : α - δ = 0
    · by_cases hv : β - ν * γ = 0
      · left
        exact ⟨by linear_combination -hu, by linear_combination hv⟩
      · rw [hu, zero_mul] at hIII
        rw [hu, zero_mul, mul_zero] at hIV
        have hu' : α + δ = 0 := by
          rcases mul_eq_zero.mp hIII.symm with h | h
          · exact h
          · exact (hv h).elim
        have hv' : β + ν * γ = 0 := by
          rcases mul_eq_zero.mp hIV.symm with h | h
          · exact (hv h).elim
          · exact h
        right
        exact ⟨by linear_combination hu', by linear_combination hv'⟩
    · by_cases hu' : α + δ = 0
      · rw [hu', zero_mul] at hIII
        have hv' : β + ν * γ = 0 := by
          rcases mul_eq_zero.mp hIII with h | h
          · exact (hu h).elim
          · exact h
        right
        exact ⟨by linear_combination hu', by linear_combination hv'⟩
      · exfalso
        apply hν
        refine ⟨(β - ν * γ) / (α - δ), ?_⟩
        have key : (α + δ) * (ν * (α - δ) ^ 2 - (β - ν * γ) ^ 2) = 0 := by
          linear_combination (α - δ) * hIV + (β - ν * γ) * hIII
        rcases mul_eq_zero.mp key with h | h
        · exact (hu' h).elim
        · field_simp
          linear_combination h
  · rintro (⟨h1, h2'⟩ | ⟨h1, h2'⟩)
    · have h1' : δ = α := h1
      have h2'' : β = ν * γ := h2'
      constructor
      · rw [h1', h2'']
        ring
      · rw [h1', h2'']
        ring
    · have h1' : δ = -α := h1
      have h2'' : β = -(ν * γ) := h2'
      constructor
      · rw [h1', h2'']
        ring
      · rw [h1', h2'']
        ring
theorem antiNS_conj {ν : F} {W C : SL2} (hW : IsAntiNS ν W) (hC : C ∈ nonsplitSL ν) :
    W * C * W⁻¹ = C⁻¹ := by
  obtain ⟨hW1, hW2⟩ := hW
  obtain ⟨hC1, hC2⟩ := hC
  have hdet := det_entries W
  rw [hW1, hW2] at hdet
  apply SL_ext <;>
    simp only [conj_apply_SL, inv_apply_00, inv_apply_01, inv_apply_10, inv_apply_11, hW1, hW2,
      hC1, hC2]
  · linear_combination ((C : Matrix (Fin 2) (Fin 2) F) 0 0) * hdet
  · linear_combination (-(ν * (C : Matrix (Fin 2) (Fin 2) F) 1 0)) * hdet
  · linear_combination (-(C : Matrix (Fin 2) (Fin 2) F) 1 0) * hdet
  · linear_combination ((C : Matrix (Fin 2) (Fin 2) F) 0 0) * hdet

theorem antiNS_not_mem (h2 : (2 : F) ≠ 0) {ν : F} {W : SL2} (hW : IsAntiNS ν W)
    (hν0 : ν ≠ 0) : W ∉ nonsplitSL ν := by
  rintro ⟨h1, h2'⟩
  obtain ⟨hW1, hW2⟩ := hW
  have hdet := det_entries W
  have ha : (W : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := by
    have : 2 * (W : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := by linear_combination hW1 - h1
    exact (mul_eq_zero.mp this).resolve_left h2
  have hc : (W : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have : (2 * ν) * (W : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination hW2 - h2'
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hν0)
  rw [ha, hc, zero_mul, mul_zero, sub_zero] at hdet
  exact zero_ne_one hdet


/-- The exact literal SL2 normalizer is torus or anti-torus, as soon as a
specified genuine torus element has nonzero lower-left coordinate. -/
theorem normalizer_mem_iff (h2 : (2 : F) ≠ 0) {ν : F} (hν : ¬IsSquare ν)
    {C : SL2} (hC : C ∈ nonsplitSL ν) (hy : C.val 1 0 ≠ 0) (M : SL2) :
    M ∈ Subgroup.normalizer (nonsplitSL ν : Set SL2) ↔
      M ∈ nonsplitSL ν ∨ IsAntiNS ν M := by
  constructor
  · intro hM
    exact (conj_mem_nonsplitSL_iff h2 hν hC hy M).mp
      ((Subgroup.mem_normalizer_iff.mp hM C).mp hC)
  · rintro (hM|hM)
    · exact Subgroup.le_normalizer hM
    · have hi : IsAntiNS ν M⁻¹ := by
        obtain ⟨h1,h01⟩ := hM
        constructor
        · simp only [inv_apply_00,inv_apply_11,h1,neg_neg]
        · simp only [inv_apply_01,inv_apply_10,h01,neg_mul,mul_neg,neg_neg]
      rw [Subgroup.mem_normalizer_iff]
      intro A
      constructor
      · intro hA
        rw [antiNS_conj hM hA]
        exact (nonsplitSL ν).inv_mem hA
      · intro hA
        have hh := antiNS_conj hi hA
        have he : M⁻¹*(M*A*M⁻¹)*(M⁻¹)⁻¹=A := by group
        rw [he] at hh
        exact hh.symm ▸ (nonsplitSL ν).inv_mem hA

/-- Norm−1 has a genuine finite-field solution; no oracle/choice predicate. -/
theorem exists_normForm_eq [Fintype F] (hF : ringChar F ≠ 2) {ν : F} (hν : ν ≠ 0) (c : F) :
    ∃ x y : F,x^2-ν*y^2=c := by
  have hf : (X^2-C c : F[X]).degree=2 := by
    rw [degree_sub_C (by rw [degree_X_pow]; norm_num),degree_X_pow]
    rfl
  have hg : (-(C ν)*X^2 : F[X]).degree=2 := by
    rw [neg_mul,degree_neg,degree_C_mul_X_pow 2 hν]
    rfl
  obtain ⟨a,b,h⟩ := FiniteField.exists_root_sum_quadratic hf hg
    (FiniteField.odd_card_of_char_ne_two hF)
  refine ⟨a,b,?_⟩
  simp only [eval_sub,eval_pow,eval_X,eval_C,eval_mul,eval_neg] at h
  linear_combination h

theorem exists_antiNS [Fintype F] (hF : ringChar F ≠ 2) {ν : F} (hν0 : ν ≠ 0) :
    ∃ W : SL2,IsAntiNS ν W := by
  obtain ⟨e,f,h⟩ := exists_normForm_eq hF hν0 (-1)
  refine ⟨⟨!![e,-(ν*f);f,-e],?_⟩,?_,?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination -h
  · simp
  · simp

end SymmetricSubgroupAsymptotics.PSLTwoLiteralNonsplitNormalizerStructure
