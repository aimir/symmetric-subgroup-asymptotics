import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexNonorthogonalCompanions
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularPairOrbit
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualNeighborData

/-! Every original intersecting nonadjacent singular-plane pair is
sent by an actual original D word to the normalized e0,e1/w chart.
The nonzero transverse coefficient is derived from the ORIGINAL
nonsingularity condition, not supplied as a new hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexR11Frame
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticForm CFSGOrthogonalDIndexPolarForm
open CFSGOrthogonalDIndexQuadraticNeighborPlane CFSGOrthogonalDIndexVectorCoordinates
open CFSGOrthogonalDIndexResidualNeighborData CFSGOrthogonalDIndexNonorthogonalCompanions
variable (K : Type) [Field K]

theorem exists_normalized_frame (s : ℕ)
    (P Q : Submodule K (Index (s + 5) → K))
    (hP : Module.finrank K P = 2) (hQ : Module.finrank K Q = 2)
    (hPs : ∀ x ∈ P, splitQuadraticForm K (s + 5) x = 0)
    (hQs : ∀ x ∈ Q, splitQuadraticForm K (s + 5) x = 0)
    (hmeet : P ⊓ Q ≠ ⊥)
    (hnonsingular : ¬∀ x ∈ P ⊔ Q, splitQuadraticForm K (s + 5) x = 0) :
    ∃ g : elementaryRootGroup K (s + 5), ∃ w : Index (s + 5) → K,
      P.map (Matrix.mulVecLin (g.val : Mat K (s + 5))) = leftPlane K s ∧
      Q.map (Matrix.mulVecLin (g.val : Mat K (s + 5))) = rightPlane K s w ∧
      splitQuadraticForm K (s + 5) w = 0 ∧
      (splitQuadraticForm K (s + 5)).polarBilin w (axis0 K s) = 0 ∧
      (splitQuadraticForm K (s + 5)).polarBilin w (axis1 K s) ≠ 0 := by
  obtain ⟨u, huP, huQ, hu, v, hvP, w, hwQ, hnv, _, hspanP, hspanQ, hvw⟩ :=
    exists_companions K (s + 5) P Q hP hQ hPs hQs hmeet hnonsingular
  have hsu : splitQ K u = 0 := (splitQuadraticForm_apply K (s + 5) u).symm.trans (hPs u huP)
  have hsv : splitQ K v = 0 := (splitQuadraticForm_apply K (s + 5) v).symm.trans (hPs v hvP)
  have huv : polar K u v = 0 := (splitQuadraticForm_polar K (s + 5) u v).symm.trans
    (polar_zero_of_singular _ P hPs u v huP hvP)
  obtain ⟨g, c, hgu, hgv⟩ := exists_singular_pair_frame K (s + 1) u v hu hsu hsv huv hnv
  change (g.val : Mat K (s + 5)) *ᵥ u = axis0 K s at hgu
  change (g.val : Mat K (s + 5)) *ᵥ v = c • axis0 K s + axis1 K s at hgv
  let w0 := (g.val : Mat K (s + 5)) *ᵥ w
  have hisom (x y : Index (s + 5) → K) :
      (splitQuadraticForm K (s + 5)).polarBilin ((g.val : Mat K (s + 5)) *ᵥ x)
        ((g.val : Mat K (s + 5)) *ᵥ y) = (splitQuadraticForm K (s + 5)).polarBilin x y := by
    rw [splitQuadraticForm_polar, splitQuadraticForm_polar]
    exact elementary_preserves_polar K (s + 1) g x y
  have hw0 : (splitQuadraticForm K (s + 5)).polarBilin w0 (axis0 K s) = 0 := by
    rw [← hgu]
    exact (hisom w u).trans (polar_zero_of_singular _ Q hQs w u hwQ huQ)
  have hw1 : (splitQuadraticForm K (s + 5)).polarBilin w0 (axis1 K s) ≠ 0 := by
    have he := hisom w v
    rw [hgv] at he
    change (splitQuadraticForm K (s + 5)).polarBilin w0 (c • axis0 K s + axis1 K s) =
      (splitQuadraticForm K (s + 5)).polarBilin w v at he
    rw [map_add, map_smul, hw0, smul_zero, zero_add] at he
    intro hz
    apply hvw
    exact (QuadraticMap.polar_comm (splitQuadraticForm K (s + 5) :
      (Index (s + 5) → K) → K) v w).trans (he.symm.trans hz)
  refine ⟨g, w0, ?_, ?_, ?_, hw0, hw1⟩
  · rw [← hspanP, Submodule.map_span, Set.image_pair]
    change Submodule.span K {(g.val : Mat K (s + 5)) *ᵥ u,
      (g.val : Mat K (s + 5)) *ᵥ v} = _
    rw [hgu, hgv]
    exact CFSGTwoDimensionalSubmoduleBasis.span_pair_shear (axis0 K s) (axis1 K s) c
  · rw [← hspanQ, Submodule.map_span, Set.image_pair]
    change Submodule.span K {(g.val : Mat K (s + 5)) *ᵥ u,
      (g.val : Mat K (s + 5)) *ᵥ w} = _
    rw [hgu]
    rfl
  · exact (elementary_preserves_bundledQ K (s + 1) g w).trans (hQs w hwQ)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexR11Frame
