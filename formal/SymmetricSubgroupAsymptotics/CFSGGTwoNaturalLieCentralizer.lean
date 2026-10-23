import SymmetricSubgroupAsymptotics.CFSGGTwoNaturalComponent
import SymmetricSubgroupAsymptotics.CFSGGTwoInvariantAxis
import Mathlib.Tactic.LinearCombination

/-! The literal natural group has trivial centralizer of the four
folded simple Lie matrices. The quadratic form and fixed axis reduce
the all-ring commutant to two matrices; the actual component excludes
the second one. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoNaturalLieCentralizer
open CFSGGTwoSerreMatrices CFSGGTwoNaturalCommutantClassification
open CFSGGTwoNaturalComponent CFSGGTwoInvariantAxis CFSGGTwoD4Inclusion
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexQuadraticForm
variable (K : Type) [Field K]

theorem natural_eq_one_of_lie_commutation (g : naturalGroup K)
    (hpos : ∀ i : Fin 2, (g.val : Mat K) * positive K i = positive K i * (g.val : Mat K))
    (hneg : ∀ i : Fin 2, (g.val : Mat K) * negative K i = negative K i * (g.val : Mat K)) :
    g = 1 := by
  obtain ⟨a, b, hab⟩ := commutant_eq K (g.val : Mat K) hpos hneg
  have haxis := congrFun (natural_fixes_axis K g) (pos 3)
  rw [hab, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, axisSwap_mulVec] at haxis
  have hdiff : a - b = 1 := by
    simpa [axis, pos, neg, Equiv.swap_apply_def, sub_eq_add_neg] using haxis
  have hQ := natural_preserves_Q K g (Pi.single (pos 3) (1 : K))
  rw [hab, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, axisSwap_mulVec] at hQ
  have hprod : a * b = 0 := by
    simpa [splitQuadraticForm_apply, splitQ, leftPart, rightPart, dotProduct,
      Fin.sum_univ_succ, pos, neg, Equiv.swap_apply_def, Fin.ext_iff] using hQ
  rcases mul_eq_zero.mp hprod with ha | hb
  · have hb : b = -1 := by linear_combination -hdiff + ha
    have he : (g.val : Mat K) = -axisSwap K := by
      simpa only [ha, hb, zero_smul, zero_add, neg_one_smul] using hab
    exact False.elim (natural_ne_neg_axisSwap K g he)
  · have ha : a = 1 := by simpa only [hb, sub_zero] using hdiff
    apply Subtype.ext
    apply Units.ext
    simpa only [ha, hb, one_smul, zero_smul, add_zero] using hab

end SymmetricSubgroupAsymptotics.CFSGGTwoNaturalLieCentralizer
