import SymmetricSubgroupAsymptotics.CFSGInvolutionNormImageAction
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.Submodule.Equiv

/-! Disjoint two-cycle representatives give coordinates on the actual
norm image in characteristic two. Fixed indices contribute zero.
The index type is never enumerated by a norm-bound Fintype. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGInvolutionNormPairCoordinates
open CFSGInvolutionNormImageAction
variable {I J:Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {R:Type*} [CommRing R]

def permutationLinear (p:Equiv.Perm I) : (I→R)≃ₗ[R](I→R) :=
  LinearEquiv.funCongrLeft R R p.symm

def pairVector (p:Equiv.Perm I) (rep:J→I) (j:J) :
    normImage (permutationLinear (R:=R) p).toLinearMap :=
  ⟨Pi.single (rep j) 1+permutationLinear p (Pi.single (rep j) 1),
    normImage_generator _ _⟩

def coordinates (p:Equiv.Perm I) (rep:J→I) :
    normImage (permutationLinear (R:=R) p).toLinearMap→ₗ[R](J→R) where
  toFun x j:=x.val (rep j)
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

def assemble (p:Equiv.Perm I) (rep:J→I) :
    (J→R)→ₗ[R]normImage (permutationLinear (R:=R) p).toLinearMap where
  toFun c:=∑j:J,c j • pairVector p rep j
  map_add' a b:=by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' a c:=by simp only [Pi.smul_apply,RingHom.id_apply,Finset.smul_sum,smul_smul,smul_eq_mul]

omit [Fintype I] [Fintype J] in
theorem coordinates_pairVector (p:Equiv.Perm I) (rep:J→I)
    (hinj:Function.Injective rep) (hsep:∀i j,rep i≠p (rep j)) (j:J) :
    coordinates (R:=R) p rep (pairVector p rep j)=Pi.single j 1 := by
  funext i
  have hpneq : p.symm (rep i)≠rep j := by
    intro he
    have hh := congrArg p he
    rw [Equiv.apply_symm_apply] at hh
    exact hsep i j hh
  change (Pi.single (rep j) (1:R):I→R) (rep i)+
    (Pi.single (rep j) (1:R):I→R) (p.symm (rep i))=(Pi.single j (1:R):J→R) i
  by_cases hij:i=j
  · subst i
    simp [hpneq]
  · have hrij:rep i≠rep j := fun h=>hij (hinj h)
    simp [hij,hrij,hpneq]

theorem coordinates_assemble (p:Equiv.Perm I) (rep:J→I)
    (hinj:Function.Injective rep) (hsep:∀i j,rep i≠p (rep j)) (c:J→R) :
    coordinates p rep (assemble p rep c)=c := by
  change coordinates p rep (∑j:J,c j • pairVector p rep j)=c
  simp only [map_sum,map_smul,coordinates_pairVector p rep hinj hsep]
  exact (pi_eq_sum_univ' c).symm

omit [Fintype I] [DecidableEq I] in
theorem permutationLinear_involutive (p:Equiv.Perm I) (hp:Function.Involutive p) :
    Function.Involutive (permutationLinear (R:=R) p) := by
  have hs (i:I) : p.symm i=p i := by
    apply p.injective
    rw [Equiv.apply_symm_apply,hp]
  intro x
  funext i
  change x (p.symm (p.symm i))=x i
  rw [hs,hs,hp]

theorem fixed_coordinate_zero [CharP R 2] (p:Equiv.Perm I)
    (x:normImage (permutationLinear (R:=R) p).toLinearMap) (i:I) (hi:p i=i) : x.val i=0 := by
  obtain ⟨u,hu⟩ := x.property
  change u+permutationLinear p u=x.val at hu
  have he := congrFun hu i
  change u i+u (p.symm i)=x.val i at he
  have hpi:p.symm i=i := by
    apply p.injective
    rw [Equiv.apply_symm_apply,hi]
  rw [hpi,←two_mul] at he
  have htwo:(2:R)=0 := by simpa using (CharP.cast_eq_zero R 2)
  rw [htwo,zero_mul] at he
  exact he.symm

private theorem pair_coordinate_eq (p:Equiv.Perm I) (hp:Function.Involutive p)
    (v:normImage (permutationLinear (R:=R) p).toLinearMap) (i:I) :
    v.val (p i)=v.val i := by
  obtain ⟨u,hu⟩ := v.property
  change u+permutationLinear p u=v.val at hu
  have h1 := congrFun hu (p i)
  have h2 := congrFun hu i
  change u (p i)+u (p.symm (p i))=v.val (p i) at h1
  change u i+u (p.symm i)=v.val i at h2
  rw [Equiv.symm_apply_apply] at h1
  have hs:p.symm i=p i := by
    apply p.injective
    rw [Equiv.apply_symm_apply,hp]
  rw [hs] at h2
  exact h1.symm.trans ((add_comm _ _).trans h2)

theorem coordinates_injective [CharP R 2] (p:Equiv.Perm I) (hp:Function.Involutive p)
    (rep:J→I) (hcover:∀i,p i=i∨∃j,i=rep j∨i=p (rep j)) :
    Function.Injective (coordinates (R:=R) p rep) := by
  intro x y he
  have hval (j:J) : x.val (rep j)=y.val (rep j) := congrFun he j
  suffices hraw:x.val=y.val from Subtype.ext hraw
  funext i
  rcases hcover i with hf|⟨j,hj|hj⟩
  · rw [fixed_coordinate_zero p x i hf,fixed_coordinate_zero p y i hf]
  · subst i
    exact hval j
  · rw [hj,pair_coordinate_eq p hp x,pair_coordinate_eq p hp y]
    exact hval j

def normPairEquiv [CharP R 2] (p:Equiv.Perm I) (hp:Function.Involutive p) (rep:J→I)
    (hinj:Function.Injective rep) (hsep:∀i j,rep i≠p (rep j))
    (hcover:∀i,p i=i∨∃j,i=rep j∨i=p (rep j)) :
    normImage (permutationLinear (R:=R) p).toLinearMap≃ₗ[R](J→R) :=
  LinearEquiv.ofBijective (coordinates p rep)
    ⟨coordinates_injective p hp rep hcover,fun c=>⟨assemble p rep c,coordinates_assemble p rep hinj hsep c⟩⟩

theorem normPairEquiv_apply [CharP R 2] (p:Equiv.Perm I) (hp:Function.Involutive p) (rep:J→I)
    (hinj:Function.Injective rep) (hsep:∀i j,rep i≠p (rep j))
    (hcover:∀i,p i=i∨∃j,i=rep j∨i=p (rep j))
    (x:normImage (permutationLinear (R:=R) p).toLinearMap) (j:J) :
    normPairEquiv p hp rep hinj hsep hcover x j=x.val (rep j) := rfl

end SymmetricSubgroupAsymptotics.CFSGInvolutionNormPairCoordinates
