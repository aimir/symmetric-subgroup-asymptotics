import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexNormalizedStarBridge
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularPairOrbit

/-! Moving the quadratic bridge back to the original singular axis.
The normalizing word is an actual elementary D word, and its inverse
returns the witness to the original natural space. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexStarVectorBridge
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticForm CFSGOrthogonalDIndexPolarForm
open CFSGOrthogonalDIndexTailCoordinates CFSGOrthogonalDIndexResidualCorrection
open CFSGOrthogonalDIndexVectorCoordinates CFSGOrthogonalDIndexNormalizedStarBridge
variable (K : Type) [Field K]

theorem exists_star_vector (s : ℕ) (u v w t : Index (s + 5) → K)
    (hu : u ≠ 0) (hnv : ∀ a : K, v ≠ a • u) (hnt : ∀ a : K, t ≠ a • u)
    (hQu : splitQuadraticForm K (s + 5) u = 0)
    (hQv : splitQuadraticForm K (s + 5) v = 0)
    (hQw : splitQuadraticForm K (s + 5) w = 0)
    (hQt : splitQuadraticForm K (s + 5) t = 0)
    (huv : (splitQuadraticForm K (s + 5)).polarBilin u v = 0)
    (huw : (splitQuadraticForm K (s + 5)).polarBilin u w = 0)
    (hut : (splitQuadraticForm K (s + 5)).polarBilin u t = 0)
    (hvw : (splitQuadraticForm K (s + 5)).polarBilin v w ≠ 0)
    (havoid : (splitQuadraticForm K (s + 5)).polarBilin v t = 0 ∨
      (splitQuadraticForm K (s + 5)).polarBilin w t = 0) :
    ∃ d : Index (s + 5) → K,
      splitQuadraticForm K (s + 5) d = 0 ∧
      (splitQuadraticForm K (s + 5)).polarBilin u d = 0 ∧
      (splitQuadraticForm K (s + 5)).polarBilin v d ≠ 0 ∧
      (splitQuadraticForm K (s + 5)).polarBilin w d ≠ 0 ∧
      (splitQuadraticForm K (s + 5)).polarBilin t d ≠ 0 := by
  let Q := splitQuadraticForm K (s + 5)
  have hqu : splitQ K u = 0 := (splitQuadraticForm_apply K (s + 5) u).symm.trans hQu
  have hqv : splitQ K v = 0 := (splitQuadraticForm_apply K (s + 5) v).symm.trans hQv
  have hpuv : polar K u v = 0 := (splitQuadraticForm_polar K (s + 5) u v).symm.trans huv
  obtain ⟨g, a, hgu, hgv⟩ := exists_singular_pair_frame K (s + 1) u v hu hqu hqv hpuv hnv
  let e0 : Index (s + 5) → K := Pi.single (Sum.inl 0) 1
  let e1 : Index (s + 5) → K := Pi.single (Sum.inl (tailSecondIndex (s + 3))) 1
  change (g.val : Mat K (s + 5)) *ᵥ u = e0 at hgu
  change (g.val : Mat K (s + 5)) *ᵥ v = a • e0 + e1 at hgv
  let w0 := (g.val : Mat K (s + 5)) *ᵥ w
  let t0 := (g.val : Mat K (s + 5)) *ᵥ t
  have hpol (x y : Index (s + 5) → K) :
      Q.polarBilin ((g.val : Mat K (s + 5)) *ᵥ x)
        ((g.val : Mat K (s + 5)) *ᵥ y) = Q.polarBilin x y := by
    rw [splitQuadraticForm_polar, splitQuadraticForm_polar]
    exact elementary_preserves_polar K (s + 1) g x y
  have hbuW : Q.polarBilin e0 w0 = 0 := by
    rw [← hgu]
    exact (hpol u w).trans huw
  have hbuT : Q.polarBilin e0 t0 = 0 := by
    rw [← hgu]
    exact (hpol u t).trans hut
  have hw00 : w0 (Sum.inr 0) = 0 := (positive_polar K (s + 5) 0 w0).symm.trans hbuW
  have ht00 : t0 (Sum.inr 0) = 0 := (positive_polar K (s + 5) 0 t0).symm.trans hbuT
  have hw1 : Q.polarBilin w0 e1 ≠ 0 := by
    have hh := hpol v w
    rw [hgv] at hh
    change Q.polarBilin (a • e0 + e1) w0 = Q.polarBilin v w at hh
    rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      hbuW, smul_zero, zero_add] at hh
    intro hz
    apply hvw
    exact hh.symm.trans ((QuadraticMap.polar_comm (Q : (Index (s + 5) → K) → K) _ _).trans hz)
  have hgi : Function.Injective (fun x => (g.val : Mat K (s + 5)) *ᵥ x) := by
    intro x y he
    have hh := congrArg (fun z => (↑(g.val⁻¹) : Mat K (s + 5)) *ᵥ z) he
    simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] using hh
  have htind : ∀ c : K, t0 ≠ c • e0 := by
    intro c he
    apply hnt c
    apply hgi
    change (g.val : Mat K (s + 5)) *ᵥ t = (g.val : Mat K (s + 5)) *ᵥ (c • u)
    rw [Matrix.mulVec_smul, hgu]
    exact he
  have hav : Q.polarBilin e1 t0 = 0 ∨ Q.polarBilin w0 t0 = 0 := by
    rcases havoid with hv0 | hw0
    · left
      have hh := hpol v t
      rw [hgv] at hh
      change Q.polarBilin (a • e0 + e1) t0 = Q.polarBilin v t at hh
      rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        hbuT, smul_zero, zero_add] at hh
      exact hh.trans hv0
    · exact Or.inr ((hpol w t).trans hw0)
  obtain ⟨d0, hdQ, hud, hvd, hwd, htd⟩ := exists_bridge_vector K (s + 1) w0 t0
    ((elementary_preserves_bundledQ K (s + 1) g w).trans hQw) hw00 hw1
    ((elementary_preserves_bundledQ K (s + 1) g t).trans hQt) ht00 htind hav
  let d := (↑(g.val⁻¹) : Mat K (s + 5)) *ᵥ d0
  have hgd : (g.val : Mat K (s + 5)) *ᵥ d = d0 := by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hd : Q d = 0 :=
    (elementary_preserves_bundledQ K (s + 1) g⁻¹ d0).trans hdQ
  have hUd : Q.polarBilin u d = 0 := by
    have hh := hpol u d
    rw [hgu, hgd] at hh
    exact hh.symm.trans hud
  have hVd : Q.polarBilin v d ≠ 0 := by
    have hh := hpol v d
    rw [hgv, hgd] at hh
    change Q.polarBilin (a • e0 + e1) d0 = Q.polarBilin v d at hh
    rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      hud, smul_zero, zero_add] at hh
    exact hh.symm.trans_ne hvd
  have hWd : Q.polarBilin w d ≠ 0 := by
    have hh := hpol w d
    rw [hgd] at hh
    exact hh.symm.trans_ne hwd
  have hTd : Q.polarBilin t d ≠ 0 := by
    have hh := hpol t d
    rw [hgd] at hh
    exact hh.symm.trans_ne htd
  exact ⟨d, hd, hUd, hVd, hWd, hTd⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexStarVectorBridge
