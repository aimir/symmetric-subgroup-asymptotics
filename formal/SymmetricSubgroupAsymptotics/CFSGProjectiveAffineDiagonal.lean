import SymmetricSubgroupAsymptotics.CFSGProjectiveAffineFibres
import SymmetricSubgroupAsymptotics.CFSGAffineCoordinateExtraction

/-! The fixed projective frame forces the actual affine permutation to
use one common coordinate permutation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveAffineChart
open CFSGProjectiveFrameCoordinates
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

theorem point_zero : point (0 : n→F)=basisPoint (F:=F) (Sum.inl ()) := by
  have he : vector (0 : n→F)=(Pi.single (Sum.inl ()) 1 : Vector (F:=F) (n:=n)) := by
    funext i
    rcases i with u | i
    · cases u
      simp only [vector_zeroCoord,Pi.single_eq_same]
    · simp only [vector_coord,Pi.zero_apply,Pi.single_apply,Sum.inr_ne_inl,↓reduceIte]
  simp only [point,basisPoint,he]

theorem point_one (b : Unit⊕n) : point (fun _ : n => (1:F))=sumPoint (F:=F) b := by
  have he : vector (fun _ : n => (1:F))=(fun _ : Unit⊕n => (1:F)) := by
    funext i
    rcases i with u | i
    · cases u
      rfl
    · rfl
  simp only [point,sumPoint,he]

private theorem constant_onLine (a : F) :
    OnLine (point (fun _ : n => a)) (point (0 : n→F)) (point (fun _ : n => (1:F))) := by
  change (F ∙ vector (fun _ : n => a))≤(F ∙ vector (0 : n→F)) ⊔
    (F ∙ vector (fun _ : n => (1:F)))
  apply (Submodule.span_singleton_le_iff_mem _ _).mpr
  apply Submodule.mem_sup.mpr
  refine ⟨(1-a) • vector (0 : n→F),Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _),
    a • vector (fun _ : n => (1:F)),Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _),?_⟩
  funext i
  rcases i with u | i
  · cases u
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,vector_zeroCoord,mul_one]
    exact sub_add_cancel 1 a
  · simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,vector_coord,Pi.zero_apply,mul_zero,mul_one,zero_add]

private theorem coordinate_eq_of_onLine (v : n→F)
    (hv : OnLine (point v) (point (0 : n→F)) (point (fun _ : n => (1:F))))
    (i j : n) : v i=v j := by
  change (F ∙ vector v)≤(F ∙ vector (0 : n→F)) ⊔ (F ∙ vector (fun _ : n => (1:F))) at hv
  have hm := ((Submodule.span_singleton_le_iff_mem _ _).mp hv)
  obtain ⟨x,hx,y,hy,he⟩ := Submodule.mem_sup.mp hm
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hi := congrArg (fun x : Vector (F:=F) (n:=n) => x (Sum.inr i)) he
  have hj := congrArg (fun x : Vector (F:=F) (n:=n) => x (Sum.inr j)) he
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,vector_coord,Pi.zero_apply,mul_zero,mul_one,zero_add] at hi hj
  exact hi.symm.trans hj

theorem affinePermutation_zero
    (f : collineationGroup (F:=F) (n:=Unit⊕n))
    (hf : ∀i : Unit⊕n,f.val (basisPoint (F:=F) i)=basisPoint (F:=F) i) :
    affinePermutation f hf 0=0 := by
  apply point_injective
  rw [point_affinePermutation,point_zero,hf]

theorem affinePermutation_one
    (f : collineationGroup (F:=F) (n:=Unit⊕n))
    (hf : ∀i : Unit⊕n,f.val (basisPoint (F:=F) i)=basisPoint (F:=F) i)
    (b : Unit⊕n) (hs : f.val (sumPoint (F:=F) b)=sumPoint (F:=F) b) :
    affinePermutation f hf (fun _ : n => (1:F))=(fun _ => 1) := by
  apply point_injective
  rw [point_affinePermutation,point_one b,hs]

theorem affinePermutation_diagonal
    (f : collineationGroup (F:=F) (n:=Unit⊕n))
    (hf : ∀i : Unit⊕n,f.val (basisPoint (F:=F) i)=basisPoint (F:=F) i)
    (b : Unit⊕n) (hs : f.val (sumPoint (F:=F) b)=sumPoint (F:=F) b)
    (a : F) (i j : n) :
    affinePermutation f hf (fun _ => a) i=affinePermutation f hf (fun _ => a) j := by
  have hline := (f.property _ _ _).mpr (constant_onLine (n:=n) a)
  have hh : OnLine (point (affinePermutation f hf (fun _ : n => a)))
      (point (affinePermutation f hf 0))
      (point (affinePermutation f hf (fun _ : n => (1:F)))) := by
    simpa only [point_affinePermutation] using hline
  rw [affinePermutation_zero,affinePermutation_one f hf b hs] at hh
  exact coordinate_eq_of_onLine _ hh i j

def commonCoordinate
    (f : collineationGroup (F:=F) (n:=Unit⊕n))
    (hf : ∀i : Unit⊕n,f.val (basisPoint (F:=F) i)=basisPoint (F:=F) i)
    (i : n) : F≃F :=
  CFSGAffineCoordinateExtraction.coordinateEquiv (affinePermutation f hf)
    (affinePermutation_fibre_iff f hf) i

theorem affinePermutation_commonCoordinate
    (f : collineationGroup (F:=F) (n:=Unit⊕n))
    (hf : ∀i : Unit⊕n,f.val (basisPoint (F:=F) i)=basisPoint (F:=F) i)
    (b : Unit⊕n) (hs : f.val (sumPoint (F:=F) b)=sumPoint (F:=F) b)
    (i : n) (v : n→F) (j : n) :
    affinePermutation f hf v j=commonCoordinate f hf i (v j) := by
  exact CFSGAffineCoordinateExtraction.apply_common_coordinate _ _
    (affinePermutation_diagonal f hf b hs) i v j

end SymmetricSubgroupAsymptotics.CFSGProjectiveAffineChart
