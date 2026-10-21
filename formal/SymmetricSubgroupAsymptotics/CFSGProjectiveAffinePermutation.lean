import SymmetricSubgroupAsymptotics.CFSGProjectiveAffineChart
import SymmetricSubgroupAsymptotics.CFSGProjectiveCoordinateHyperplanes

/-! The actual affine permutation induced by a collineation fixing the
coordinate points. No coordinatewise or semilinear form is presumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveAffineChart
open CFSGProjectiveFrameCoordinates
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

private theorem outside_image
    (f : collineationGroup (F:=F) (n:=Unit⊕n))
    (hf : ∀i : Unit⊕n,f.val (basisPoint (F:=F) i)=basisPoint (F:=F) i)
    (p : Point (F:=F) (n:=n)) (hp : p∉(infinity (F:=F) (n:=n)).projectivization) :
    f.val p∉(infinity (F:=F) (n:=n)).projectivization := by
  exact fun he => hp ((mem_coordinateHyperplane_image_iff f hf (Sum.inl ()) p).mp he)

private theorem outside_inverse
    (f : collineationGroup (F:=F) (n:=Unit⊕n))
    (hf : ∀i : Unit⊕n,f.val (basisPoint (F:=F) i)=basisPoint (F:=F) i)
    (p : Point (F:=F) (n:=n)) (hp : p∉(infinity (F:=F) (n:=n)).projectivization) :
    f.val.symm p∉(infinity (F:=F) (n:=n)).projectivization := by
  intro he
  apply hp
  have hh := (mem_coordinateHyperplane_image_iff f hf (Sum.inl ()) (f.val.symm p)).mpr he
  simpa only [Equiv.apply_symm_apply] using hh

def complementEquiv
    (f : collineationGroup (F:=F) (n:=Unit⊕n))
    (hf : ∀i : Unit⊕n,f.val (basisPoint (F:=F) i)=basisPoint (F:=F) i) :
    {p : Point (F:=F) (n:=n) // p∉(infinity (F:=F) (n:=n)).projectivization}≃
      {p : Point (F:=F) (n:=n) // p∉(infinity (F:=F) (n:=n)).projectivization} where
  toFun p := ⟨f.val p.val,outside_image f hf p.val p.property⟩
  invFun p := ⟨f.val.symm p.val,outside_inverse f hf p.val p.property⟩
  left_inv p := Subtype.ext (f.val.symm_apply_apply p.val)
  right_inv p := Subtype.ext (f.val.apply_symm_apply p.val)

def affinePermutation
    (f : collineationGroup (F:=F) (n:=Unit⊕n))
    (hf : ∀i : Unit⊕n,f.val (basisPoint (F:=F) i)=basisPoint (F:=F) i) :
    Equiv.Perm (n→F) := chart.trans ((complementEquiv f hf).trans chart.symm)

theorem point_affinePermutation
    (f : collineationGroup (F:=F) (n:=Unit⊕n))
    (hf : ∀i : Unit⊕n,f.val (basisPoint (F:=F) i)=basisPoint (F:=F) i) (v : n→F) :
    point (affinePermutation f hf v)=f.val (point v) := by
  change point (coordinates (f.val (point v)))=f.val (point v)
  exact point_coordinates _ (outside_image f hf _ (point_not_infinity v))

theorem affinePermutation_coord_zero_iff
    (f : collineationGroup (F:=F) (n:=Unit⊕n))
    (hf : ∀i : Unit⊕n,f.val (basisPoint (F:=F) i)=basisPoint (F:=F) i)
    (v : n→F) (i : n) : affinePermutation f hf v i=0↔v i=0 := by
  have hh := mem_coordinateHyperplane_image_iff f hf (Sum.inr i) (point v)
  rw [←point_affinePermutation f hf v] at hh
  simpa only [point,Submodule.mk_mem_projectivization_iff,mem_coordinateHyperplane,
    vector_coord] using hh

end SymmetricSubgroupAsymptotics.CFSGProjectiveAffineChart
