import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticStarPairs
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexR11Action
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticShell

/-! Every original singular point lies on an actual R11 seed pair.
An original elementary word takes its axis to e0; the companions e1
and f1 are pulled back by the inverse word. Valid also over F2. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticForm CFSGOrthogonalDIndexQuadraticCorrection
open CFSGOrthogonalDIndexResidualCorrection CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDIndexQuadraticStarPairs CFSGOrthogonalDIndexQuadraticShell
open CFSGOrthogonalDIndexVectorCoordinates CFSGPolarCommonPointPlanes
variable (K : Type) [Field K]

theorem exists_R11_seed_at_axis (s : ℕ) (u : Index (s + 5) → K)
    (hu : u ≠ 0) (hQu : splitQuadraticForm K (s + 5) u = 0) :
    ∃ P Q : SingularPlanes K (s + 1),
      u ∈ P.val ∧ u ∈ Q.val ∧ IntersectingNonadjacent K (s + 1) P Q := by
  let A := splitQuadraticForm K (s + 5)
  let i : Fin (s + 5) := ⟨1, by omega⟩
  let e0 : Index (s + 5) → K := Pi.single (Sum.inl 0) 1
  let e1 : Index (s + 5) → K := Pi.single (Sum.inl i) 1
  let f1 : Index (s + 5) → K := Pi.single (Sum.inr i) 1
  have hi : (0 : Fin (s + 5)) ≠ i := by
    intro hh
    have hv := congrArg Fin.val hh
    change 0 = 1 at hv
    omega
  have he1 : A e1 = 0 := positive_quadratic K (s + 5) i
  have hf1 : A f1 = 0 := by
    rw [splitQuadraticForm_apply]
    simp [f1, splitQ, leftPart, rightPart, dotProduct, Pi.single_apply]
  have h01 : A.polarBilin e0 e1 = 0 := by
    rw [positive_polar]
    simp only [e1, Pi.single_apply, Sum.inr_ne_inl, if_false]
  have h0f : A.polarBilin e0 f1 = 0 := by
    rw [positive_polar]
    simp only [f1, Pi.single_apply, Sum.inr.injEq, if_neg hi]
  have h1f : A.polarBilin e1 f1 = 1 := by
    rw [positive_polar]
    simp only [f1, Pi.single_eq_same]
  obtain ⟨g, hgu⟩ := exists_normalize_singular K (s + 3) u hu
    ((splitQuadraticForm_apply K (s + 5) u).symm.trans hQu)
  change (g.val : Mat K (s + 5)) *ᵥ u = e0 at hgu
  let v := (↑(g.val⁻¹) : Mat K (s + 5)) *ᵥ e1
  let w := (↑(g.val⁻¹) : Mat K (s + 5)) *ᵥ f1
  have hgv : (g.val : Mat K (s + 5)) *ᵥ v = e1 := by
    change (g.val : Mat K (s + 5)) *ᵥ ((↑(g.val⁻¹) : Mat K (s + 5)) *ᵥ e1) = e1
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hgw : (g.val : Mat K (s + 5)) *ᵥ w = f1 := by
    change (g.val : Mat K (s + 5)) *ᵥ ((↑(g.val⁻¹) : Mat K (s + 5)) *ᵥ f1) = f1
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hpol (x y : Index (s + 5) → K) :
      A.polarBilin ((g.val : Mat K (s + 5)) *ᵥ x)
        ((g.val : Mat K (s + 5)) *ᵥ y) = A.polarBilin x y := by
    rw [splitQuadraticForm_polar, splitQuadraticForm_polar]
    exact elementary_preserves_polar_all_ranks K (s + 5) (by omega) g x y
  have hvQ : A v = 0 := (elementary_preserves_bundledQ K (s + 1) g⁻¹ e1).trans he1
  have hwQ : A w = 0 := (elementary_preserves_bundledQ K (s + 1) g⁻¹ f1).trans hf1
  have huv : A.polarBilin u v = 0 := by
    have hh := hpol u v
    rw [hgu, hgv, h01] at hh
    exact hh.symm
  have huw : A.polarBilin u w = 0 := by
    have hh := hpol u w
    rw [hgu, hgw, h0f] at hh
    exact hh.symm
  have hvw : A.polarBilin v w ≠ 0 := by
    have hh := hpol v w
    rw [hgv, hgw, h1f] at hh
    exact hh.symm.trans_ne one_ne_zero
  have hnv : ∀ a : K, v ≠ a • u := by
    intro a he
    apply hvw
    simp only [he, map_smul, LinearMap.smul_apply, huw, smul_zero]
  have hnw : ∀ a : K, w ≠ a • u := by
    intro a he
    have hvu : A.polarBilin v u = 0 :=
      (QuadraticMap.polar_comm (A : (Index (s + 5) → K) → K) _ _).trans huv
    apply hvw
    simp only [he, map_smul, hvu, smul_zero]
  let P : SingularPlanes K (s + 1) := ⟨Submodule.span K {u, v},
    pairPlane_finrank u v hu hnv, singular_span_pair A u v hQu hvQ huv⟩
  let Q : SingularPlanes K (s + 1) := ⟨Submodule.span K {u, w},
    pairPlane_finrank u w hu hnw, singular_span_pair A u w hQu hwQ huw⟩
  have huP : u ∈ P.val := Submodule.subset_span (Or.inl rfl)
  have huQ : u ∈ Q.val := Submodule.subset_span (Or.inl rfl)
  exact ⟨P, Q, huP, huQ,
    intersecting_nonsingular_of_pairing A P.val Q.val P.property.1 Q.property.1
      P.property.2 Q.property.2 u v w hu huP huQ
      (Submodule.subset_span (Or.inr rfl)) (Submodule.subset_span (Or.inr rfl)) hvw⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneFamilyAction
