import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSingleDegreeSpan
import Mathlib.Tactic.NoncommRing

/-! The leading layer of an ordered matrix-unit word is additive at
EVERY positive integer height, before any root-space or characteristic
assumption. Literal integer degree cuts, not field-valued weights, are used.
This is a leading-coefficient theorem, not ordered-product surjectivity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixHighLayerProducts
open CFSGGradedMatrixSingleDegreeSpan
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

def BelowCut (weight : I→ℤ) (h : ℤ) (M : Matrix I I K) : Prop :=
  ∀i j,weight i<weight j+h→M i j=0

theorem belowCut_add (weight : I→ℤ) (h : ℤ) (M N : Matrix I I K)
    (hM : BelowCut weight h M) (hN : BelowCut weight h N) : BelowCut weight h (M+N) := by
  intro i j hij
  rw [Matrix.add_apply,hM i j hij,hN i j hij,zero_add]

theorem belowCut_mono (weight : I→ℤ) (h k : ℤ) (M : Matrix I I K)
    (hhk : h≤k) (hM : BelowCut weight k M) : BelowCut weight h M := by
  intro i j hij
  exact hM i j (by omega)

theorem belowCut_mul (weight : I→ℤ) (h k : ℤ) (M N : Matrix I I K)
    (hM : BelowCut weight h M) (hN : BelowCut weight k N) : BelowCut weight (h+k) (M*N) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro t ht
  by_cases hit : weight i<weight t+h
  · rw [hM i t hit,zero_mul]
  · have htj : weight t<weight j+k := by omega
    rw [hN t j htj,mul_zero]

theorem degreePart_mul_zero (weight : I→ℤ) (d h k : ℤ) (M N : Matrix I I K)
    (hd : d<h+k) (hM : BelowCut weight h M) (hN : BelowCut weight k N) :
    degreePart weight d (M*N)=0 := by
  apply Matrix.ext
  intro i j
  change (if weight i=weight j+d then (M*N) i j else 0)=0
  by_cases hij : weight i=weight j+d
  · rw [if_pos hij]
    exact belowCut_mul weight h k M N hM hN i j (by omega)
  · rw [if_neg hij]

theorem leading_deviation_mul (weight : I→ℤ) (h : ℤ) (hh : 0<h)
    (u v : (Matrix I I K)ˣ)
    (hu : BelowCut weight h ((u : Matrix I I K)-1))
    (hv : BelowCut weight h ((v : Matrix I I K)-1)) :
    BelowCut weight h (((u*v : (Matrix I I K)ˣ) : Matrix I I K)-1) ∧
      degreePart weight h (((u*v : (Matrix I I K)ˣ) : Matrix I I K)-1)=
        degreePart weight h ((u : Matrix I I K)-1)+degreePart weight h ((v : Matrix I I K)-1) := by
  have he : (u : Matrix I I K)*(v : Matrix I I K)-1=
      ((u : Matrix I I K)-1)+((v : Matrix I I K)-1)+
        ((u : Matrix I I K)-1)*((v : Matrix I I K)-1) := by noncomm_ring
  constructor
  · change BelowCut weight h ((u : Matrix I I K)*(v : Matrix I I K)-1)
    rw [he]
    exact belowCut_add weight h _ _ (belowCut_add weight h _ _ hu hv)
      (belowCut_mono weight h (h+h) _ (by omega) (belowCut_mul weight h h _ _ hu hv))
  · change degreePart weight h ((u : Matrix I I K)*(v : Matrix I I K)-1)=_
    rw [he,map_add,map_add,degreePart_mul_zero weight h h h _ _ (by omega) hu hv,add_zero]

theorem ordered_leading_layer (weight : I→ℤ) (h : ℤ) (hh : 0<h)
    (l : List (Matrix I I K)ˣ)
    (hl : ∀u∈l,BelowCut weight h ((u : Matrix I I K)-1)) :
    BelowCut weight h (((l.prod : (Matrix I I K)ˣ) : Matrix I I K)-1) ∧
      degreePart weight h (((l.prod : (Matrix I I K)ˣ) : Matrix I I K)-1)=
        (l.map (fun (u : (Matrix I I K)ˣ)=>degreePart weight h ((u : Matrix I I K)-1))).sum := by
  revert hl
  induction l with
  | nil=>
    intro hl
    constructor
    · intro i j hij
      simp only [List.prod_nil,Units.val_one,sub_self,Matrix.zero_apply]
    · simp only [List.prod_nil,Units.val_one,sub_self,map_zero,List.map_nil,List.sum_nil]
  | cons u l ih=>
    intro hl
    have hu := hl u (by simp)
    have htail : ∀v∈l,BelowCut weight h ((v : Matrix I I K)-1) := fun v hv=>hl v (by simp [hv])
    obtain ⟨hprod,hpart⟩ := ih htail
    obtain ⟨hcut,hvalue⟩ := leading_deviation_mul weight h hh u l.prod hu hprod
    refine ⟨hcut,?_⟩
    rw [List.prod_cons,hvalue,hpart,List.map_cons,List.sum_cons]

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixHighLayerProducts
