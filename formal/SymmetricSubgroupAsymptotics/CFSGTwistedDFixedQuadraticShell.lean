import SymmetricSubgroupAsymptotics.CFSGTwistedDSingularDimensionBound
import SymmetricSubgroupAsymptotics.CFSGTwistedDPlaneRootLine
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorParametrization
import SymmetricSubgroupAsymptotics.CFSGTwistedA2NormSurjectivity

/-! Every shell of the actual fixed quadratic form pairs surjectively
with a nonzero singular axis. The final anisotropic norm plane realizes
any fixed-field quadratic value, so even the genuine rank-two base
works over F2. No second split hyperbolic pair is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedQuadraticShell
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticForm CFSGOrthogonalDIndexPrefixPerpendicular
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDPlaneRootLine CFSGTwistedDSingularDimensionBound
open CFSGTwistedDFixedVectorParametrization CFSGTwistedA2FixedField CFSGSerreOrdinaryTwists

theorem exists_shell_at_axis (n : ℕ) (q : CFSG.PrimePower) (c d : fixedField q) :
    ∃ z : fixedSpace n q, fixedQuadraticForm n q z = c ∧
      (fixedQuadraticForm n q).polarBilin (firstAxis n q) z = d := by
  have hc : definingFieldAutomorphism q 2 (c : q.Extension 2) = (c : q.Extension 2) := c.property
  obtain ⟨a, ha⟩ := CFSGTwistedA2UnipotentArrays.exists_norm_eq_fixed q (c : q.Extension 2) hc
  let p : Parameters n q := ((fun _ => 0), (Pi.single (0 : Fin (n + 1)) d, a))
  let z : fixedSpace n q := ⟨fromParameters n q p, fromParameters_fixed n q p⟩
  have hz0 : z.val (Sum.inr 0) = (d : q.Extension 2) := by
    change fromParameters n q p (Sum.inr (0 : Fin (n + 1)).castSucc) = _
    rw [fromParameters, Fin.lastCases_castSucc]
    change ((Pi.single (0 : Fin (n + 1)) d : Fin (n + 1) → fixedField q) 0 : q.Extension 2) = _
    rw [Pi.single_eq_same]
  refine ⟨z, ?_, ?_⟩
  · apply Subtype.ext
    rw [fixedQuadraticForm_apply, splitQuadraticForm_apply]
    change (∑ i : Fin (n + 2), fromParameters n q p (Sum.inl i) *
      fromParameters n q p (Sum.inr i)) = (c : q.Extension 2)
    rw [Fin.sum_univ_castSucc]
    simp only [fromParameters, Fin.lastCases_castSucc, Fin.lastCases_last,
      p, ZeroMemClass.coe_zero, zero_mul, Finset.sum_const_zero, zero_add]
    exact ha
  · apply Subtype.ext
    rw [fixedQuadraticForm_polar, splitQuadraticForm_polar]
    change CFSGOrthogonalDIndexPolarForm.polar (q.Extension 2)
      (Pi.single (Sum.inl 0) 1) z.val = (d : q.Extension 2)
    rw [polar_positive_basis]
    exact hz0

theorem exists_quadratic_polar_values (n : ℕ) (q : CFSG.PrimePower)
    (v : fixedSpace n q) (hv : v ≠ 0) (hs : fixedQuadraticForm n q v = 0)
    (c d : fixedField q) :
    ∃ z : fixedSpace n q, fixedQuadraticForm n q z = c ∧
      (fixedQuadraticForm n q).polarBilin v z = d := by
  have hvK := congrArg (fun a : fixedField q => (a : q.Extension 2)) hs
  dsimp only at hvK
  rw [fixedQuadraticForm_apply] at hvK
  obtain ⟨g, hg⟩ := CFSGTwistedDAllRankSingularOrbit.exists_normalize_all n q v.val v.property hvK
    (fun he => hv (Subtype.ext he))
  have hgv : fixedLinearHom n q g v = firstAxis n q := by
    apply Subtype.ext
    rw [fixedLinearHom_apply]
    exact hg
  obtain ⟨t, htQ, htB⟩ := exists_shell_at_axis n q c d
  let z := (fixedLinearHom n q g).symm t
  have hgz : fixedLinearHom n q g z = t := (fixedLinearHom n q g).apply_symm_apply t
  refine ⟨z, ?_, ?_⟩
  · exact (fixedLinearHom_preserves_Q n q g z).symm.trans (by rw [hgz]; exact htQ)
  · have hb := fixedLinearHom_preserves_polar n q g v z
    rw [hgv, hgz] at hb
    exact hb.symm.trans htB

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedQuadraticShell
