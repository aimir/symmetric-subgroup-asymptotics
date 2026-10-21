import SymmetricSubgroupAsymptotics.CFSGProjectiveFrameImageBasis

/-! The final point of the literal image coordinate frame has no zero
coordinate in its actual image basis. The proof transports each original
coordinate hyperplane; it does not assume semilinear classification. -/
set_option autoImplicit false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveFrameAlignment
open CFSGProjectiveFrameCoordinates CFSGProjectiveSpanRepresentatives
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

theorem imageBasis_span_projectivization (f : collineationGroup (F := F) (n := n))
    (s : Set n) :
    (Submodule.span F ((imageBasis f) '' s)).projectivization =
      mapSubspace f (Projectivization.Subspace.span (basisPoint (F := F) '' s)) := by
  have h := projectivization_span_representatives (fun i : s => f.val (basisPoint i.val))
  have hL : Set.range (fun i : s => (f.val (basisPoint i.val)).rep) = (imageBasis f) '' s := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.property, imageBasis_apply f i.val⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, (imageBasis_apply f i).symm⟩
  have hR : Set.range (fun i : s => f.val (basisPoint i.val)) =
      f.val '' (basisPoint (F := F) '' s) := by
    ext p
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨basisPoint i.val, ⟨i.val, i.property, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [hL, hR] at h
  exact h.trans (mapSubspace_span f _).symm

theorem image_final_coordinate_ne_zero (f : collineationGroup (F := F) (n := n))
    (b i : n) : (imageBasis f).repr (f.val (sumPoint b)).rep i ≠ 0 := by
  intro hz
  have hv : (f.val (sumPoint b)).rep ∈
      Submodule.span F ((imageBasis f) '' {j : n | j ≠ i}) := by
    apply (imageBasis f).mem_span_image.mpr
    intro j hj
    change j ≠ i
    intro hji
    subst j
    exact (Finsupp.mem_support_iff.mp hj) hz
  have hp := (Submodule.mk_mem_projectivization_iff _
    (f.val (sumPoint b)).rep_nonzero).mpr hv
  rw [Projectivization.mk_rep, imageBasis_span_projectivization] at hp
  have hpre := (mem_mapSubspace f _ (f.val (sumPoint b))).mp hp
  have hsum : sumPoint (F := F) b ∈
      Projectivization.Subspace.span (basisPoint (F := F) '' {j : n | j ≠ i}) := by
    simpa only [Equiv.symm_apply_apply] using hpre
  rw [← coordinateHyperplane_projective_span] at hsum
  have hnz : (fun _ : n => (1 : F)) ≠ 0 := by
    intro hzero
    exact one_ne_zero (congrFun hzero b)
  change Projectivization.mk F (fun _ : n => (1 : F)) hnz ∈
    (coordinateHyperplane (F := F) i).projectivization at hsum
  have hc := (Submodule.mk_mem_projectivization_iff _ hnz).mp hsum
  exact one_ne_zero (show (1 : F) = 0 from hc)

end SymmetricSubgroupAsymptotics.CFSGProjectiveFrameAlignment
