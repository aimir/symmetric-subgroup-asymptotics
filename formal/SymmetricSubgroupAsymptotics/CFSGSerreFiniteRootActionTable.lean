import SymmetricSubgroupAsymptotics.CFSGSerreRootLoweringComparison
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Finite coefficient tables for a sparse original-source height
induction. Only raises on the support of an already known lowering
are needed. A finite coefficient equality then determines the new
source raise at positive weight, or the new lowering of a known
nonzero-scalar parent path. Neither a basis nor faithfulness is assumed.
Actual integral table entries remain obligations of each application. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSerreFiniteRootActionTable
open CFSG.Models.Chevalley CFSGSerreSignedRootWeights CFSGSerreRootLoweringComparison
variable {r:ℕ} {I:Type*} [Fintype I] [DecidableEq I]
    (A:Matrix (Fin r) (Fin r) ℤ) (x:I→RationalLie A)
local notation "L" => RationalLie A
local notation "lc" => Fintype.linearCombination ℚ x

omit [DecidableEq I] in
theorem raising_combination (neg:Bool) (i:Fin r) (d:I→ℚ) (e:I→I→ℚ)
    (he:∀l,d l≠0→⁅rootVector A neg i,x l⁆=lc (e l)) :
    ⁅rootVector A neg i,lc d⁆=lc (∑l,d l • e l) := by
  change ⁅rootVector A neg i,∑l,d l • x l⁆=lc (∑l,d l • e l)
  rw [lie_sum,map_sum]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hz:d l=0
  · simp only [hz,zero_smul,lie_zero,map_zero]
  · rw [lie_smul,he l hz,map_smul]

theorem lowering_raising_table (neg:Bool) (i a:Fin r) (j:I) (mu:ℚ)
    (hw:⁅coroot A neg a,x j⁆=mu • x j)
    (d:I→ℚ) (e:I→I→ℚ) (t:I→ℚ)
    (hd:⁅oppositeVector A neg a,x j⁆=lc d)
    (he:∀l,d l≠0→⁅rootVector A neg i,x l⁆=lc (e l))
    (hcoeff:(if a=i then (-mu) • Pi.single j 1 else 0)+(∑l,d l • e l)=t) :
    ⁅oppositeVector A neg a,⁅rootVector A neg i,x j⁆⁆=lc t := by
  have h:=opposite_raising A neg i a (x j) mu hw
  rw [hd,raising_combination A x neg i d e he] at h
  have hdelta:(if a=i then -(mu • x j) else 0)=
      lc (if a=i then (-mu) • Pi.single j 1 else 0) := by
    by_cases hai:a=i
    · simp only [if_pos hai]
      rw [map_smul,Fintype.linearCombination_apply_single,one_smul,neg_smul]
    · simp only [if_neg hai,map_zero]
  rw [hdelta,←map_add,hcoeff] at h
  exact h

theorem raising_eq_of_lowering_coefficients (neg:Bool) (i a:Fin r) (haa:A a a=2)
    (j:I) (mu:ℚ) (hpositive:0<(A a i:ℚ)+mu) (w:L)
    (hwj:⁅coroot A neg a,x j⁆=mu • x j)
    (hww:⁅coroot A neg a,w⁆=((A a i:ℚ)+mu) • w)
    (d:I→ℚ) (e:I→I→ℚ) (t:I→ℚ)
    (hd:⁅oppositeVector A neg a,x j⁆=lc d)
    (he:∀l,d l≠0→⁅rootVector A neg i,x l⁆=lc (e l))
    (ht:⁅oppositeVector A neg a,w⁆=lc t)
    (hcoeff:(if a=i then (-mu) • Pi.single j 1 else 0)+(∑l,d l • e l)=t) :
    ⁅rootVector A neg i,x j⁆=w := by
  have hweight:⁅coroot A neg a,⁅rootVector A neg i,x j⁆⁆=
      ((A a i:ℚ)+mu) • ⁅rootVector A neg i,x j⁆ := by
    rw [leibniz_lie,coroot_root,hwj,smul_lie,lie_smul,add_smul]
  exact eq_of_positive_weight_of_opposite_eq A neg a haa _ w _ hpositive hweight hww
    ((lowering_raising_table A x neg i a j mu hwj d e t hd he hcoeff).trans ht.symm)

theorem lowering_of_raising_path (neg:Bool) (i a:Fin r) (j:I) (mu:ℚ)
    (hw:⁅coroot A neg a,x j⁆=mu • x j)
    (w:L) (c:ℚ) (hc:c≠0) (hpath:⁅rootVector A neg i,x j⁆=c • w)
    (d:I→ℚ) (e:I→I→ℚ) (f:I→ℚ)
    (hd:⁅oppositeVector A neg a,x j⁆=lc d)
    (he:∀l,d l≠0→⁅rootVector A neg i,x l⁆=lc (e l))
    (hcoeff:(if a=i then (-mu) • Pi.single j 1 else 0)+(∑l,d l • e l)=c • f) :
    ⁅oppositeVector A neg a,w⁆=lc f := by
  have h:=lowering_raising_table A x neg i a j mu hw d e (c • f) hd he hcoeff
  rw [hpath,lie_smul,map_smul] at h
  exact (smul_right_injective L hc) h

end SymmetricSubgroupAsymptotics.CFSGSerreFiniteRootActionTable
