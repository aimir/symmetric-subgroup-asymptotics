import SymmetricSubgroupAsymptotics.CFSGInvolutionNormPairCoordinates
import Mathlib.Algebra.Module.Submodule.EqLocus
import Mathlib.LinearAlgebra.Isomorphisms

/-! The literal fixed-space quotient by the norm image of an index
involution has coordinates at its fixed indices in characteristic two.
The other indices are covered by selected disjoint two-cycles. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGInvolutionFixedNormQuotientCoordinates
open CFSGInvolutionNormImageAction CFSGInvolutionNormPairCoordinates
variable {I J:Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {R:Type*} [CommRing R]

def FixedIndex (p:Equiv.Perm I) := {i:I // p i=i}

def fixedSpace (p:Equiv.Perm I) : Submodule R (I→R) :=
  LinearMap.eqLocus (permutationLinear (R:=R) p).toLinearMap LinearMap.id

def normInFixed (p:Equiv.Perm I) : Submodule R (fixedSpace (R:=R) p) :=
  (normImage (permutationLinear (R:=R) p).toLinearMap).comap (fixedSpace p).subtype

def fixedCoordinates (p:Equiv.Perm I) :
    fixedSpace (R:=R) p→ₗ[R](FixedIndex p→R) where
  toFun x i:=x.val i.val
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

omit [Fintype I] in
private theorem extend_fixed (p:Equiv.Perm I) (c:FixedIndex p→R) :
    permutationLinear p (fun i=>if hi:p i=i then c ⟨i,hi⟩ else 0)=
      (fun i=>if hi:p i=i then c ⟨i,hi⟩ else 0) := by
  funext i
  change (if hi:p (p.symm i)=p.symm i then c ⟨p.symm i,hi⟩ else 0)=
    (if hi:p i=i then c ⟨i,hi⟩ else 0)
  by_cases hi:p i=i
  · have hs:p.symm i=i := by
      apply p.injective
      rw [Equiv.apply_symm_apply,hi]
    simp only [hs,dif_pos hi]
  · have hs:¬p (p.symm i)=p.symm i := by
      intro he
      apply hi
      simpa only [Equiv.apply_symm_apply] using congrArg p he
    simp only [dif_neg hi,dif_neg hs]

def extendFixed (p:Equiv.Perm I) : (FixedIndex p→R)→ₗ[R]fixedSpace (R:=R) p where
  toFun c:=⟨fun i=>if hi:p i=i then c ⟨i,hi⟩ else 0,extend_fixed p c⟩
  map_add' a b:=by
    apply Subtype.ext
    funext i
    by_cases hi:p i=i <;> simp [hi]
  map_smul' a c:=by
    apply Subtype.ext
    funext i
    by_cases hi:p i=i <;> simp [hi]

omit [Fintype I] in
theorem fixedCoordinates_extendFixed (p:Equiv.Perm I) (c:FixedIndex p→R) :
    fixedCoordinates p (extendFixed p c)=c := by
  funext i
  change (if hi:p i.val=i.val then c ⟨i.val,hi⟩ else 0)=c i
  simp only [dif_pos i.property]
  exact congrArg c (Subtype.ext rfl)

theorem fixedCoordinates_surjective (p:Equiv.Perm I) :
    Function.Surjective (fixedCoordinates (R:=R) p) :=
  fun c=>⟨extendFixed p c,fixedCoordinates_extendFixed p c⟩

omit [Fintype I] [DecidableEq I] in
private theorem fixed_value (p:Equiv.Perm I) (v:I→R)
    (hv:permutationLinear p v=v) (i:I) : v (p i)=v i := by
  have he:=congrFun hv (p i)
  change v (p.symm (p i))=v (p i) at he
  rw [Equiv.symm_apply_apply] at he
  exact he.symm

omit [Fintype I] [DecidableEq I] in
private theorem norm_value (p:Equiv.Perm I) (hp:Function.Involutive p)
    (v:normImage (permutationLinear (R:=R) p).toLinearMap) (i:I) :
    v.val (p i)=v.val i := by
  obtain ⟨u,hu⟩:=v.property
  change u+permutationLinear p u=v.val at hu
  have h1:=congrFun hu (p i)
  have h2:=congrFun hu i
  change u (p i)+u (p.symm (p i))=v.val (p i) at h1
  change u i+u (p.symm i)=v.val i at h2
  rw [Equiv.symm_apply_apply] at h1
  have hs:p.symm i=p i := by
    apply p.injective
    rw [Equiv.apply_symm_apply,hp]
  rw [hs] at h2
  exact h1.symm.trans ((add_comm _ _).trans h2)

theorem fixedCoordinates_ker [CharP R 2] (p:Equiv.Perm I) (hp:Function.Involutive p)
    (rep:J→I) (hinj:Function.Injective rep) (hsep:∀i j,rep i≠p (rep j))
    (hcover:∀i,p i=i∨∃j,i=rep j∨i=p (rep j)) :
    (fixedCoordinates (R:=R) p).ker=normInFixed (R:=R) p := by
  ext x
  change fixedCoordinates p x=0 ↔ x.val∈normImage (permutationLinear p).toLinearMap
  constructor
  · intro hx
    let c:J→R:=fun j=>x.val (rep j)
    let v:normImage (permutationLinear (R:=R) p).toLinearMap:=assemble p rep c
    have hcoords:coordinates p rep v=c:=coordinates_assemble p rep hinj hsep c
    have hvalues (j:J):v.val (rep j)=x.val (rep j):=congrFun hcoords j
    have hraw:x.val=v.val := by
      funext i
      rcases hcover i with hf|⟨j,hj|hj⟩
      · have hzero:x.val i=0:=congrFun hx ⟨i,hf⟩
        rw [hzero,fixed_coordinate_zero p v i hf]
      · subst i
        exact (hvalues j).symm
      · rw [hj,fixed_value p x.val x.property,norm_value p hp v]
        exact (hvalues j).symm
    rw [hraw]
    exact v.property
  · intro hx
    funext i
    exact fixed_coordinate_zero p ⟨x.val,hx⟩ i.val i.property

def fixedNormQuotientEquiv [CharP R 2] (p:Equiv.Perm I) (hp:Function.Involutive p)
    (rep:J→I) (hinj:Function.Injective rep) (hsep:∀i j,rep i≠p (rep j))
    (hcover:∀i,p i=i∨∃j,i=rep j∨i=p (rep j)) :
    (fixedSpace (R:=R) p ⧸ normInFixed (R:=R) p)≃ₗ[R](FixedIndex p→R) :=
  (Submodule.quotEquivOfEq _ _ (fixedCoordinates_ker (R:=R) p hp rep hinj hsep hcover).symm).trans
    ((fixedCoordinates (R:=R) p).quotKerEquivOfSurjective (fixedCoordinates_surjective p))

theorem fixedNormQuotientEquiv_mk [CharP R 2] (p:Equiv.Perm I) (hp:Function.Involutive p)
    (rep:J→I) (hinj:Function.Injective rep) (hsep:∀i j,rep i≠p (rep j))
    (hcover:∀i,p i=i∨∃j,i=rep j∨i=p (rep j)) (x:fixedSpace (R:=R) p) :
    fixedNormQuotientEquiv (R:=R) p hp rep hinj hsep hcover (Submodule.Quotient.mk x)=
      fixedCoordinates p x := by
  simp only [fixedNormQuotientEquiv,LinearEquiv.trans_apply,Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

end SymmetricSubgroupAsymptotics.CFSGInvolutionFixedNormQuotientCoordinates
