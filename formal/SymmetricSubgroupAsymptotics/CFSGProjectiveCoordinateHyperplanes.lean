import SymmetricSubgroupAsymptotics.CFSGProjectiveCollineationSpans
import Mathlib.LinearAlgebra.StdBasis

/-! A collineation fixing the coordinate points preserves each original
coordinate hyperplane. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveFrameCoordinates
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

theorem basisPoint_span (I : Set n) :
    Projectivization.Subspace.span (basisPoint (F:=F) '' I)=
      (Submodule.span F ((fun i : n => (Pi.single i 1 : n→F)) '' I)).projectivization := by
  let L := Submodule.span F ((fun i : n => (Pi.single i 1 : n→F)) '' I)
  let S := Projectivization.Subspace.span (basisPoint (F:=F) '' I)
  apply le_antisymm
  · apply Projectivization.Subspace.span_le_subspace_iff.mpr
    rintro _ ⟨i,hi,rfl⟩
    exact (Submodule.mk_mem_projectivization_iff L _).mpr
      (Submodule.subset_span ⟨i,hi,rfl⟩)
  · have hL : L≤Projectivization.Subspace.submodule S := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,hi,rfl⟩
      apply (Projectivization.Subspace.mem_submodule_iff S _).mpr
      exact Projectivization.Subspace.subset_span _ ⟨i,hi,rfl⟩
    simpa only [Submodule.projectivization,OrderIso.symm_apply_apply] using
      Submodule.projectivization.monotone hL

def coordinateHyperplane (i : n) : Submodule F (n→F) :=
  LinearMap.ker (LinearMap.proj i)

@[simp] theorem mem_coordinateHyperplane (i : n) (v : n→F) :
    v∈coordinateHyperplane (F:=F) i↔v i=0 := Iff.rfl

theorem coordinateHyperplane_eq_span (i : n) :
    coordinateHyperplane (F:=F) i=
      Submodule.span F ((fun j : n => (Pi.single j 1 : n→F)) '' {j | j≠i}) := by
  let b := Pi.basisFun F n
  have hb : (fun j : n => (Pi.single j 1 : n→F))=b := by
    funext j
    exact (Pi.basisFun_apply F n j).symm
  rw [hb]
  apply le_antisymm
  · intro v hv
    apply b.mem_span_image.mpr
    intro j hj
    change j≠i
    intro he
    subst j
    have hne : b.repr v i≠0 := Finsupp.mem_support_iff.mp hj
    exact hne (by rw [Pi.basisFun_repr];exact hv)
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,hji,rfl⟩
    change b j i=0
    simp only [b,Pi.basisFun_apply,Pi.single_apply]
    exact if_neg (Ne.symm hji)

theorem coordinateHyperplane_projective_span (i : n) :
    (coordinateHyperplane (F:=F) i).projectivization=
      Projectivization.Subspace.span (basisPoint (F:=F) '' {j | j≠i}) := by
  rw [basisPoint_span,coordinateHyperplane_eq_span]

theorem map_coordinateHyperplane (f : collineationGroup (F:=F) (n:=n))
    (hf : ∀i : n,f.val (basisPoint (F:=F) i)=basisPoint (F:=F) i) (i : n) :
    mapSubspace f (coordinateHyperplane (F:=F) i).projectivization=
      (coordinateHyperplane (F:=F) i).projectivization := by
  rw [coordinateHyperplane_projective_span]
  apply mapSubspace_span_eq_of_fixed
  rintro _ ⟨j,hj,rfl⟩
  exact hf j

theorem mem_coordinateHyperplane_image_iff (f : collineationGroup (F:=F) (n:=n))
    (hf : ∀i : n,f.val (basisPoint (F:=F) i)=basisPoint (F:=F) i)
    (i : n) (p : Points (F:=F) (n:=n)) :
    f.val p∈(coordinateHyperplane (F:=F) i).projectivization↔
      p∈(coordinateHyperplane (F:=F) i).projectivization := by
  have he := mem_mapSubspace f (coordinateHyperplane (F:=F) i).projectivization (f.val p)
  simpa only [map_coordinateHyperplane f hf,Equiv.symm_apply_apply] using he

end SymmetricSubgroupAsymptotics.CFSGProjectiveFrameCoordinates
