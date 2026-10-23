import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeCyclicSpan
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeSignedGroups
import SymmetricSubgroupAsymptotics.CFSGTwistedDNormalizeFirstPair
import SymmetricSubgroupAsymptotics.CFSGMatrixCyclicCentralizer
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! The centre of the literal relative-root subgroup is scalar. The
actual singular-prefix tests give one eigenaxis; literal relative
singular-vector normalization propagates it, and the paired terminal
words separate the two remaining axes. No full fixed-group recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeCenter
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDRelativeSignedGroups
open CFSGTwistedDSingularPrefix CFSGTwistedDNaturalQuadraticTwist
open CFSGOrthogonalDIndexUnipotent CFSGTwistedDRelativeFixedGroup
open CFSGOrthogonalDIndexBundledQuadratic CFSGSerreOrdinaryTwists
open CFSGMatrixCyclicCentralizer

private theorem upper_fixes_first (K : Type) [Field K] (n : ℕ)
    (u : (Mat K (n + 2))ˣ)
    (hu : u ∈ CFSGMatrixFlagSubgroups.unipotentUnits (K := K) (flagEquiv (n + 2))) :
    (u : Mat K (n + 2)) *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1 := by
  rw [Matrix.mulVec_single_one]
  funext x
  by_cases hx : x = Sum.inl (0 : Fin (n + 2))
  · subst x
    simpa only [Matrix.col, Pi.single_eq_same] using hu.2 (Sum.inl 0)
  · have hne : (flagEquiv (n + 2) x).val ≠ 0 := by
      intro h
      apply hx
      apply (flagEquiv (n + 2)).injective
      apply Fin.ext
      exact h
    have hlt : flagEquiv (n + 2) (Sum.inl 0) < flagEquiv (n + 2) x := by
      change 0 < (flagEquiv (n + 2) x).val
      omega
    simpa only [Matrix.col, Pi.single_eq_of_ne hx] using hu.1 hlt

theorem central_commutes (n : ℕ) (q : CFSG.PrimePower)
    (u : relativeRootGroup n q) (hu : u ∈ Subgroup.center (relativeRootGroup n q))
    (v : relativeRootGroup n q) :
    (u.val : Mat (q.Extension 2) (n + 2)) * (v.val : Mat (q.Extension 2) (n + 2)) =
      (v.val : Mat (q.Extension 2) (n + 2)) * (u.val : Mat (q.Extension 2) (n + 2)) :=
  congrArg (fun z : relativeRootGroup n q => (z.val : Mat (q.Extension 2) (n + 2)))
    ((Subgroup.mem_center_iff.mp hu v).symm)

theorem central_first_axis (n : ℕ) (q : CFSG.PrimePower)
    (u : relativeRootGroup n q) (hu : u ∈ Subgroup.center (relativeRootGroup n q)) :
    ∃ c : q.Extension 2,
      (u.val : Mat (q.Extension 2) (n + 2)) *ᵥ Pi.single (Sum.inl 0) 1 =
        c • Pi.single (Sum.inl 0) 1 := by
  let K := q.Extension 2
  let e : Index (n + 2) → K := Pi.single (Sum.inl 0) 1
  let w := (u.val : Mat K (n + 2)) *ᵥ e
  have hQ : splitQuadraticForm K (n + 2) w = 0 := by
    rw [splitQuadraticForm_apply]
    exact (CFSGOrthogonalDAllRankQuadraticPreservation.elementary_preserves K n
      ⟨u.val, relativeRootGroup_le_elementary n q u.property⟩ e).trans
        ((splitQuadraticForm_apply K (n + 2) e).symm.trans
          (CFSGSplitQuadraticBasisParameters.positive_norm K 0 1))
  have htest (g : (Mat K (n + 2))ˣ)
      (hg : g ∈ signedRootGroup n q false) :
      (g : Mat K (n + 2)) *ᵥ w - w ∈ positivePrefix K n 0 := by
    have hr : g ∈ relativeRootGroup n q := by
      rw [← positive_sup_negative n q]
      exact (show signedRootGroup n q false ≤
        signedRootGroup n q false ⊔ signedRootGroup n q true from le_sup_left) hg
    have hc := central_commutes n q u hu ⟨g, hr⟩
    have he := upper_fixes_first K n g (positive_le_upper_units n q hg)
    change (g : Mat K (n + 2)) *ᵥ ((u.val : Mat K (n + 2)) *ᵥ e) - w ∈ _
    rw [Matrix.mulVec_mulVec, ← hc, ← Matrix.mulVec_mulVec, he, sub_self]
    exact (positivePrefix K n 0).zero_mem
  have hw : w ∈ positivePrefix K n 1 := by
    apply prefix_succ_of_singular_fixed K n 0 (Nat.zero_le _) w hQ
    · intro i
      exact htest _ (Subgroup.subset_closure (Or.inl ⟨i, (1 : CFSGTwistedA2FixedField.fixedField q), rfl⟩))
    · have h := htest (pairedRoot n q false 1)
        (Subgroup.subset_closure (Or.inr ⟨1, rfl⟩))
      simpa only [pairedRoot, CFSGTwistedDForkPositiveAction.foldedFork, map_one] using h
  refine ⟨w (Sum.inl 0), ?_⟩
  change w = _
  funext x
  by_cases hx : x = Sum.inl (0 : Fin (n + 2))
  · subst x
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  · have hn : (flagEquiv (n + 2) x).val ≠ 0 := by
      intro h
      apply hx
      apply (flagEquiv (n + 2)).injective
      apply Fin.ext
      exact h
    have hz := hw x (by omega)
    simpa only [Pi.smul_apply, Pi.single_eq_of_ne hx, smul_zero] using hz

theorem relativeRootGroup_center_iff_scalar (n : ℕ) (q : CFSG.PrimePower)
    (u : relativeRootGroup n q) :
    u ∈ Subgroup.center (relativeRootGroup n q) ↔
      ∃ c : q.Extension 2, (u.val : Mat (q.Extension 2) (n + 2)) = c • 1 := by
  constructor
  · intro hu
    obtain ⟨c, hc⟩ := central_first_axis n q u hu
    let A : Mat (q.Extension 2) (n + 2) := u.val
    let S := Module.End.eigenspace (Matrix.mulVecLin A) c
    have hsing (v : Index (n + 2) → q.Extension 2)
        (hv : vectorTwist (q.Extension 2) n (definingFieldAutomorphism q 2) v = v)
        (hQ : splitQuadraticForm (q.Extension 2) (n + 2) v = 0) : v ∈ S := by
      rw [Module.End.mem_eigenspace_iff]
      change A *ᵥ v = c • v
      by_cases hz : v = 0
      · simp only [hz, Matrix.mulVec_zero, smul_zero]
      obtain ⟨a, ha⟩ := CFSGTwistedDAllRankSingularOrbit.exists_normalize_all n q v hv hQ hz
      have hb : (↑(a.val⁻¹) : Mat (q.Extension 2) (n + 2)) *ᵥ
          Pi.single (Sum.inl 0) 1 = v := by
        rw [← ha, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      rw [← hb]
      exact eigenvector_of_commutes A _ (central_commutes n q u hu a⁻¹) _ c hc
    have hb (i : Fin (n + 2)) (hi : i ≠ last n) :
        (Pi.single (Sum.inl i) 1 : Index (n + 2) → q.Extension 2) ∈ S ∧
        (Pi.single (Sum.inr i) 1 : Index (n + 2) → q.Extension 2) ∈ S := by
      constructor
      · exact hsing _ (CFSGTwistedDNormalizeFirstPair.fixed_basis _ n _ _
          (by rw [CFSGTwistedDNaturalFork.flip_pos, if_neg hi]))
          (CFSGSplitQuadraticBasisParameters.positive_norm _ i 1)
      · exact hsing _ (CFSGTwistedDNormalizeFirstPair.fixed_basis _ n _ _
          (by rw [CFSGTwistedDNaturalFork.flip_neg, if_neg hi]))
          (CFSGSplitQuadraticBasisParameters.negative_norm _ i 1)
    have hS : S = ⊤ := CFSGTwistedDRelativeCyclicSpan.eq_top_of_relative_words n q S hb (by
      intro a
      rw [Module.End.mem_eigenspace_iff]
      exact eigenvector_of_commutes A _
        (central_commutes n q u hu ⟨pairedRoot n q false a, paired_mem n q false a⟩)
        _ c (Module.End.mem_eigenspace_iff.mp (hb (pen n) (pen_ne_last n)).2))
    refine ⟨c, Matrix.ext_of_mulVec_single ?_⟩
    intro x
    have hx : (Pi.single x 1 : Index (n + 2) → q.Extension 2) ∈ S := by rw [hS]; trivial
    simpa only [Matrix.smul_mulVec, Matrix.one_mulVec] using
      (Module.End.mem_eigenspace_iff.mp hx)
  · rintro ⟨c, hc⟩
    apply Subgroup.mem_center_iff.mpr
    intro v
    apply Subtype.ext
    apply Units.ext
    change (v.val : Mat (q.Extension 2) (n + 2)) * (u.val : Mat (q.Extension 2) (n + 2)) =
      (u.val : Mat (q.Extension 2) (n + 2)) * (v.val : Mat (q.Extension 2) (n + 2))
    rw [hc]
    simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeCenter
