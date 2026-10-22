import SymmetricSubgroupAsymptotics.CFSGGeneratedOrbitConstancy
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDSimpleMaximalOverlap
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexMaximalSpaceOrbit
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryElements
import SymmetricSubgroupAsymptotics.CFSGMatrixSubspaceUnitAction

/-! The actual maximal Q-singular D spaces are connected by overlaps of
codimension at most two. The elementary group has two orbits, so the proof
retains its crossed alternative and the literal codimension-one bridge.
No transitivity between the two components is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDMaximalOverlapConstancy
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexQuadraticSubspacePoints
open CFSGOrthogonalDIsometryIndexMaximalSpaceOrbit CFSGOrthogonalDIsometryIndexCrossingSpaces
open CFSGOrthogonalDBinaryElements CFSGOrthogonalDSimpleMaximalOverlap
variable (K : Type) [Field K]

theorem rootElements_generate (r : ℕ) :
    Subgroup.closure {u : elementaryRootGroup K r | ∃neg i a,u=rootElement K r neg i a}=⊤ := by
  let H := Subgroup.closure {u : elementaryRootGroup K r | ∃neg i a,u=rootElement K r neg i a}
  have hle : elementaryRootGroup K r≤H.map (elementaryRootGroup K r).subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨neg,i,a,rfl⟩
    exact ⟨rootElement K r neg i a,Subgroup.subset_closure ⟨neg,i,a,rfl⟩,rfl⟩
  apply top_unique
  intro u _
  obtain ⟨v,hv,he⟩ := hle u.property
  exact (Subtype.ext he : v=u) ▸ hv

theorem naturalSubspace_inf_finrank (r : ℕ) (hr : 2≤r) (g : elementaryRootGroup K r)
    (W Z : Subspaces (splitQuadraticForm K r)) :
    Module.finrank K ((naturalSubspace K r hr g W).val⊓
      (naturalSubspace K r hr g Z).val : Submodule K (Index r→K))=
        Module.finrank K (W.val⊓Z.val : Submodule K (Index r→K)) := by
  change Module.finrank K (W.val.map (naturalLinearHom K r g).toLinearMap⊓
    Z.val.map (naturalLinearHom K r g).toLinearMap : Submodule K (Index r→K))=_
  rw [←Submodule.map_inf _ (naturalLinearHom K r g).injective,
    (naturalLinearHom K r g).finrank_map_eq]

theorem constant_on_maximal_spaces {Y : Type*} (r : ℕ) (hr : 2≤r)
    (φ : Subspaces (splitQuadraticForm K r)→Y)
    (hlocal : ∀W Z : Subspaces (splitQuadraticForm K r),
      Module.finrank K W.val=r → Module.finrank K Z.val=r →
      r≤Module.finrank K (W.val⊓Z.val : Submodule K (Index r→K))+2 → φ W=φ Z)
    (W : Subspaces (splitQuadraticForm K r)) (hW : Module.finrank K W.val=r) :
    φ W=φ ⟨positiveSpace K r,fun x hx=>positiveSpace_singular K r ⟨x,hx⟩⟩ := by
  let P : Subspaces (splitQuadraticForm K r) :=
    ⟨positiveSpace K r,fun x hx=>positiveSpace_singular K r ⟨x,hx⟩⟩
  let F : elementaryRootGroup K r→Y := fun g=>φ (naturalSubspace K r hr g P)
  have hstep : ∀a ε i t,F (a*rootElement K r ε i t)=F a := by
    intro a ε i t
    let b := rootElement K r ε i t
    let e := naturalLinearHom K r a
    have hmap : (naturalSubspace K r hr (a*b) P).val=
        (naturalSubspace K r hr b P).val.map e.toLinearMap := by
      change P.val.map (Matrix.mulVecLin ((a.val : Mat K r)*(b.val : Mat K r)))=_
      rw [Matrix.mulVecLin_mul,Submodule.map_comp]
      rfl
    have hd : Module.finrank K ((naturalSubspace K r hr a P).val⊓
        (naturalSubspace K r hr (a*b) P).val : Submodule K (Index r→K))=
        Module.finrank K (P.val⊓(naturalSubspace K r hr b P).val : Submodule K (Index r→K)) := by
      rw [hmap]
      change Module.finrank K (P.val.map e.toLinearMap⊓
        (naturalSubspace K r hr b P).val.map e.toLinearMap : Submodule K (Index r→K))=_
      rw [←Submodule.map_inf e.toLinearMap e.injective,e.finrank_map_eq]
    have hb : r≤Module.finrank K ((naturalSubspace K r hr a P).val⊓
        (naturalSubspace K r hr (a*b) P).val : Submodule K (Index r→K))+2 := by
      rw [hd]
      exact root_positive_intersection_finrank K r ε i t
    exact (hlocal (naturalSubspace K r hr a P) (naturalSubspace K r hr (a*b) P)
      ((naturalSubspace_finrank K r hr a P).trans (positiveSpace_finrank K r))
      ((naturalSubspace_finrank K r hr (a*b) P).trans (positiveSpace_finrank K r)) hb).symm
  have hF : ∀g,F g=F 1 := CFSGGeneratedOrbitConstancy.constant_of_generating_right_steps
    _ (rootElements_generate K r) F (by rintro a b ⟨ε,i,t,rfl⟩;exact hstep a ε i t)
  have hP : naturalSubspace K r hr 1 P=P := by
    apply Subtype.ext
    exact CFSGMatrixSubspaceUnitAction.map_one P.val
  have hconst (g : elementaryRootGroup K r) : φ (naturalSubspace K r hr g P)=φ P :=
    (hF g).trans (congrArg φ hP)
  obtain ⟨g,hg | ⟨j,hg⟩⟩ := exists_normalize_full_rank K r hr W hW
  · have hi := congrArg (fun T : Submodule K (Index r→K)=>
        T.map (Matrix.mulVecLin ((g.val⁻¹ : (Mat K r)ˣ) : Mat K r))) hg
    change (W.val.map (Matrix.mulVecLin (g.val : Mat K r))).map
      (Matrix.mulVecLin ((g.val⁻¹ : (Mat K r)ˣ) : Mat K r)) = _ at hi
    rw [←CFSGMatrixSubspaceUnitAction.map_mul,inv_mul_cancel,Units.val_one,
      CFSGMatrixSubspaceUnitAction.map_one] at hi
    have he : W=naturalSubspace K r hr g⁻¹ P := Subtype.ext hi
    exact (congrArg φ he).trans (hconst g⁻¹)
  · let C : Subspaces (splitQuadraticForm K r) :=
      ⟨crossingSpace K r j,crossingSpace_singular K r j⟩
    have hi := congrArg (fun T : Submodule K (Index r→K)=>
        T.map (Matrix.mulVecLin ((g.val⁻¹ : (Mat K r)ˣ) : Mat K r))) hg
    change (W.val.map (Matrix.mulVecLin (g.val : Mat K r))).map
      (Matrix.mulVecLin ((g.val⁻¹ : (Mat K r)ˣ) : Mat K r)) = _ at hi
    rw [←CFSGMatrixSubspaceUnitAction.map_mul,inv_mul_cancel,Units.val_one,
      CFSGMatrixSubspaceUnitAction.map_one] at hi
    have he : W=naturalSubspace K r hr g⁻¹ C := Subtype.ext hi
    have hc := crossing_distance_one K r j
    change r-Module.finrank K (P.val⊓C.val : Submodule K (Index r→K))=1 at hc
    have hb : r≤Module.finrank K ((naturalSubspace K r hr g⁻¹ P).val⊓
        (naturalSubspace K r hr g⁻¹ C).val : Submodule K (Index r→K))+2 := by
      rw [naturalSubspace_inf_finrank]
      omega
    have hl := hlocal (naturalSubspace K r hr g⁻¹ P) (naturalSubspace K r hr g⁻¹ C)
      ((naturalSubspace_finrank K r hr g⁻¹ P).trans (positiveSpace_finrank K r))
      ((naturalSubspace_finrank K r hr g⁻¹ C).trans (crossingSpace_finrank K r j)) hb
    exact (congrArg φ he).trans (hl.symm.trans (hconst g⁻¹))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDMaximalOverlapConstancy
