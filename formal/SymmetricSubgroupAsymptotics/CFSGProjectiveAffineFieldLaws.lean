import SymmetricSubgroupAsymptotics.CFSGProjectiveAffineDiagonal
import SymmetricSubgroupAsymptotics.CFSGFieldPermutationOperations

/-! Two original projective-line configurations force the common
coordinate permutation of a fixed-frame collineation to be a field automorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveAffineChart
open CFSGProjectiveFrameCoordinates
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

private theorem onLine_affine_combination (p q : n→F) (t : F) :
    OnLine (point ((1-t) • p+t • q)) (point p) (point q) := by
  change (F ∙ vector ((1-t) • p+t • q))≤(F ∙ vector p) ⊔ (F ∙ vector q)
  apply (Submodule.span_singleton_le_iff_mem _ _).mpr
  apply Submodule.mem_sup.mpr
  refine ⟨(1-t) • vector p,Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _),
    t • vector q,Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _),?_⟩
  funext k
  rcases k with u | k
  · cases u
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,vector_zeroCoord,mul_one]
    exact sub_add_cancel 1 t
  · rfl

private theorem determinant_of_onLine (p q r : n→F)
    (hr : OnLine (point r) (point p) (point q)) (i j : n) :
    (q i-p i)*(r j-p j)=(q j-p j)*(r i-p i) := by
  change (F ∙ vector r)≤(F ∙ vector p) ⊔ (F ∙ vector q) at hr
  obtain ⟨x,hx,y,hy,he⟩ := Submodule.mem_sup.mp ((Submodule.span_singleton_le_iff_mem _ _).mp hr)
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hy
  have h0 := congrArg (fun x : Vector (F:=F) (n:=n) => x (Sum.inl ())) he
  have hab : a+b=1 := by
    simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,vector_zeroCoord,mul_one] using h0
  have ha : a=1-b := eq_sub_of_add_eq hab
  have hi := congrArg (fun x : Vector (F:=F) (n:=n) => x (Sum.inr i)) he
  have hj := congrArg (fun x : Vector (F:=F) (n:=n) => x (Sum.inr j)) he
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,vector_coord,ha] at hi hj
  rw [←hi,←hj]
  ring

private theorem determinant_common
    (f : collineationGroup (F:=F) (n:=Unit⊕n))
    (hf : ∀k : Unit⊕n,f.val (basisPoint (F:=F) k)=basisPoint (F:=F) k)
    (b0 : Unit⊕n) (hs : f.val (sumPoint (F:=F) b0)=sumPoint (F:=F) b0)
    (i0 : n) (p q r : n→F) (hr : OnLine (point r) (point p) (point q)) (i j : n) :
    (commonCoordinate f hf i0 (q i)-commonCoordinate f hf i0 (p i))*
      (commonCoordinate f hf i0 (r j)-commonCoordinate f hf i0 (p j))=
    (commonCoordinate f hf i0 (q j)-commonCoordinate f hf i0 (p j))*
      (commonCoordinate f hf i0 (r i)-commonCoordinate f hf i0 (p i)) := by
  have hh : OnLine (point (affinePermutation f hf r))
      (point (affinePermutation f hf p)) (point (affinePermutation f hf q)) := by
    simpa only [point_affinePermutation] using (f.property _ _ _).mpr hr
  simpa only [affinePermutation_commonCoordinate f hf b0 hs i0] using
    determinant_of_onLine _ _ _ hh i j

private def plane (i j : n) (a b : F) : n→F := Pi.single i a+Pi.single j b

private theorem commonCoordinate_zero
    (f : collineationGroup (F:=F) (n:=Unit⊕n))
    (hf : ∀k : Unit⊕n,f.val (basisPoint (F:=F) k)=basisPoint (F:=F) k) (i : n) :
    commonCoordinate f hf i 0=0 :=
  CFSGAffineCoordinateExtraction.coordinateEquiv_zero _ _ (affinePermutation_zero f hf) i

private theorem commonCoordinate_one
    (f : collineationGroup (F:=F) (n:=Unit⊕n))
    (hf : ∀k : Unit⊕n,f.val (basisPoint (F:=F) k)=basisPoint (F:=F) k)
    (b0 : Unit⊕n) (hs : f.val (sumPoint (F:=F) b0)=sumPoint (F:=F) b0) (i : n) :
    commonCoordinate f hf i 1=1 :=
  CFSGAffineCoordinateExtraction.coordinateEquiv_one _ _ (affinePermutation_one f hf b0 hs) i

theorem commonCoordinate_mul
    (f : collineationGroup (F:=F) (n:=Unit⊕n))
    (hf : ∀k : Unit⊕n,f.val (basisPoint (F:=F) k)=basisPoint (F:=F) k)
    (b0 : Unit⊕n) (hs : f.val (sumPoint (F:=F) b0)=sumPoint (F:=F) b0)
    (i j : n) (hij : i≠j) (a b : F) :
    commonCoordinate f hf i (a*b)=commonCoordinate f hf i a*commonCoordinate f hf i b := by
  have hh := determinant_common f hf b0 hs i 0 (plane i j 1 a)
    ((1-b) • (0 : n→F)+b • plane i j 1 a)
    (onLine_affine_combination 0 (plane i j 1 a) b) i j
  simpa [plane,Pi.single_apply,hij,Ne.symm hij,commonCoordinate_zero,
    commonCoordinate_one f hf b0 hs,mul_comm] using hh

theorem commonCoordinate_complement
    (f : collineationGroup (F:=F) (n:=Unit⊕n))
    (hf : ∀k : Unit⊕n,f.val (basisPoint (F:=F) k)=basisPoint (F:=F) k)
    (b0 : Unit⊕n) (hs : f.val (sumPoint (F:=F) b0)=sumPoint (F:=F) b0)
    (i j : n) (hij : i≠j) (a : F) :
    commonCoordinate f hf i (1-a)=1-commonCoordinate f hf i a := by
  have hh := determinant_common f hf b0 hs i (plane i j 1 0) (plane i j 0 1)
    ((1-(1-a)) • plane i j 1 0+(1-a) • plane i j 0 1)
    (onLine_affine_combination (plane i j 1 0) (plane i j 0 1) (1-a)) i j
  have hn : (1 : F)-(1-a)=a := by ring
  have he : -commonCoordinate f hf i (1-a)=commonCoordinate f hf i a-1 := by
    simpa [plane,Pi.single_apply,hij,Ne.symm hij,hn,commonCoordinate_zero,
      commonCoordinate_one f hf b0 hs] using hh
  apply neg_injective
  rw [he]
  ring

def coordinateRingAut
    (f : collineationGroup (F:=F) (n:=Unit⊕n))
    (hf : ∀k : Unit⊕n,f.val (basisPoint (F:=F) k)=basisPoint (F:=F) k)
    (b0 : Unit⊕n) (hs : f.val (sumPoint (F:=F) b0)=sumPoint (F:=F) b0)
    (i j : n) (hij : i≠j) : F≃+*F :=
  CFSGFieldPermutationOperations.ringAutOfOperations (commonCoordinate f hf i)
    (commonCoordinate_zero f hf i) (commonCoordinate_one f hf b0 hs i)
    (commonCoordinate_mul f hf b0 hs i j hij)
    (commonCoordinate_complement f hf b0 hs i j hij)

theorem affinePermutation_coordinateRingAut
    (f : collineationGroup (F:=F) (n:=Unit⊕n))
    (hf : ∀k : Unit⊕n,f.val (basisPoint (F:=F) k)=basisPoint (F:=F) k)
    (b0 : Unit⊕n) (hs : f.val (sumPoint (F:=F) b0)=sumPoint (F:=F) b0)
    (i j : n) (hij : i≠j) (v : n→F) (k : n) :
    affinePermutation f hf v k=coordinateRingAut f hf b0 hs i j hij (v k) :=
  affinePermutation_commonCoordinate f hf b0 hs i v k

end SymmetricSubgroupAsymptotics.CFSGProjectiveAffineChart
