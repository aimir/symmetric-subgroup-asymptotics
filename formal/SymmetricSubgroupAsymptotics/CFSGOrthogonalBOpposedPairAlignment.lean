import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOpposedAlignment

/-! TWO actual opposed full-rank singular spaces are simultaneously
aligned with the literal positive/negative spaces by SAME original
B elementary words, hence also by a determinant-one isometry. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOpposedPairAlignment
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPositiveSubspace CFSGOrthogonalBUnipotent
open CFSGOrthogonalBMaximalSubspaceOrbit CFSGOrthogonalBOpposedGraphShear
open CFSGPolarSubspacePoints
variable (K : Type) [Field K] [Finite K]

theorem exists_align_opposed_pair (h2 : (2 : K) ≠ 0) (s : ℕ)
    (P Q : Subspaces (gram K (s + 1)).toBilin')
    (hPdim : Module.finrank K P.val = s + 1) (hQdim : Module.finrank K Q.val = s + 1)
    (hdis : Disjoint P.val Q.val) :
    ∃ g : elementaryRootGroup K (s + 1),
      P.val.map (Matrix.mulVecLin (g.val : Mat K (s + 1))) = positiveSubspace K (s + 1) ∧
      Q.val.map (Matrix.mulVecLin (g.val : Mat K (s + 1))) = negativeSubspace K (s + 1) := by
  obtain ⟨a, ha⟩ := exists_normalize_full_rank K h2 (s + 1) P hPdim
  let Q' := naturalSubspace K h2 (s + 1) a Q
  have hQ'dim : Module.finrank K Q'.val = s + 1 :=
    (naturalSubspace_finrank K h2 (s + 1) a Q).trans hQdim
  have hQ'dis : Disjoint Q'.val (positiveSubspace K (s + 1)) := by
    change Disjoint (Q.val.map (Matrix.mulVecLin (a.val : Mat K (s + 1)))) _
    rw [← ha]
    exact Submodule.disjoint_map (CFSGOrthogonalBSingularVectorCount.naturalLinearEquiv K (s + 1) a).injective hdis.symm
  obtain ⟨b, hbf, hbQ⟩ :=
    CFSGOrthogonalBOpposedAlignment.exists_stabilizer_align_opposed K h2 s Q' hQ'dis hQ'dim
  have hbP : (positiveSubspace K (s + 1)).map
      (Matrix.mulVecLin (b.val : Mat K (s + 1))) = positiveSubspace K (s + 1) := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      change (b.val : Mat K (s + 1)) *ᵥ u ∈ positiveSubspace K (s + 1)
      rw [hbf u hu]
      exact hu
    · intro hv
      exact ⟨v, hv, hbf v hv⟩
  refine ⟨b * a, ?_, ?_⟩
  · change P.val.map (Matrix.mulVecLin
      ((b.val * a.val : (Mat K (s + 1))ˣ) : Mat K (s + 1))) = _
    rw [CFSGMatrixSubspaceUnitAction.map_mul, ha, hbP]
  · change Q.val.map (Matrix.mulVecLin
      ((b.val * a.val : (Mat K (s + 1))ˣ) : Mat K (s + 1))) = _
    rw [CFSGMatrixSubspaceUnitAction.map_mul]
    exact hbQ

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOpposedPairAlignment
