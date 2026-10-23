import SymmetricSubgroupAsymptotics.CFSGSerreCrossNodeCommutation
import SymmetricSubgroupAsymptotics.CFSGSerreFixedRootElements

/-! A three-node orthogonal orbit gives a literal fixed root word in
the ORIGINAL twist graph. The cyclic rearrangement uses original
integral-lattice root commutation. Neither derived membership nor
generation of the fixed subgroup is inferred. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreTripleFixedRoots
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (K : Type) [Field K]
    (perm : Fin n→Fin n) (exponent : Fin n→ℕ)

theorem triple_root_mem_fixed (neg : Bool) (i : Fin n)
    (hi₁ : A i (perm i)=0) (hi₂ : A i (perm (perm i))=0)
    (hpi : perm (perm (perm i))=i) (t : K)
    (ht : ((t^exponent i)^exponent (perm i))^exponent (perm (perm i))=t) :
    ((modelRoot A K neg i t)*
      (modelRoot A K neg (perm i) (t^exponent i))*
      (modelRoot A K neg (perm (perm i)) ((t^exponent i)^exponent (perm i)))).val ∈
        fixedSubgroup A K perm exponent := by
  let u:=modelRoot A K neg i t
  let v:=modelRoot A K neg (perm i) (t^exponent i)
  let w:=modelRoot A K neg (perm (perm i)) ((t^exponent i)^exponent (perm i))
  have huv : (u.val,v.val)∈twistGraph A K perm exponent :=
    Subgroup.subset_closure ⟨neg,i,t,rfl,rfl⟩
  have hvw : (v.val,w.val)∈twistGraph A K perm exponent :=
    Subgroup.subset_closure ⟨neg,perm i,t^exponent i,rfl,rfl⟩
  have hwu : (w.val,u.val)∈twistGraph A K perm exponent := by
    apply Subgroup.subset_closure
    refine ⟨neg,perm (perm i),(t^exponent i)^exponent (perm i),rfl,?_⟩
    change IsRootElement A K neg (perm (perm (perm i)))
      (((t^exponent i)^exponent (perm i))^exponent (perm (perm i))) u.val
    rw [hpi,ht]
    rfl
  have hc₁ : u.val*v.val=v.val*u.val := congrArg (fun g : Model A K=>g.val)
    (CFSGSerreCrossNodeCommutation.modelRoots_commute_of_cartan_zero A K neg i (perm i)
      hi₁ t (t^exponent i)).eq
  have hc₂ : u.val*w.val=w.val*u.val := congrArg (fun g : Model A K=>g.val)
    (CFSGSerreCrossNodeCommutation.modelRoots_commute_of_cartan_zero A K neg i (perm (perm i))
      hi₂ t ((t^exponent i)^exponent (perm i))).eq
  have hcycle : v.val*w.val*u.val=u.val*v.val*w.val := by
    calc
      v.val*w.val*u.val=v.val*(w.val*u.val) := mul_assoc _ _ _
      _=v.val*(u.val*w.val) := congrArg (fun x=>v.val*x) hc₂.symm
      _=(v.val*u.val)*w.val := (mul_assoc _ _ _).symm
      _=(u.val*v.val)*w.val := congrArg (fun x=>x*w.val) hc₁.symm
  refine ⟨(u*v*w).property,?_⟩
  have hm:=(twistGraph A K perm exponent).mul_mem
    ((twistGraph A K perm exponent).mul_mem huv hvw) hwu
  change (u.val*v.val*w.val,v.val*w.val*u.val)∈_ at hm
  change (u.val*v.val*w.val,u.val*v.val*w.val)∈twistGraph A K perm exponent
  rwa [hcycle] at hm

def tripleFixedRoot (neg : Bool) (i : Fin n)
    (hi₁ : A i (perm i)=0) (hi₂ : A i (perm (perm i))=0)
    (hpi : perm (perm (perm i))=i) (t : K)
    (ht : ((t^exponent i)^exponent (perm i))^exponent (perm (perm i))=t) :
    fixedSubgroup A K perm exponent :=
  ⟨((modelRoot A K neg i t)*modelRoot A K neg (perm i) (t^exponent i)*
    modelRoot A K neg (perm (perm i)) ((t^exponent i)^exponent (perm i))).val,
    triple_root_mem_fixed A K perm exponent neg i hi₁ hi₂ hpi t ht⟩

theorem tripleFixedRoot_toModel (neg : Bool) (i : Fin n)
    (hi₁ : A i (perm i)=0) (hi₂ : A i (perm (perm i))=0)
    (hpi : perm (perm (perm i))=i) (t : K)
    (ht : ((t^exponent i)^exponent (perm i))^exponent (perm (perm i))=t) :
    CFSGSerreFixedRootElements.fixedToModel A K perm exponent
      (tripleFixedRoot A K perm exponent neg i hi₁ hi₂ hpi t ht)=
        modelRoot A K neg i t*modelRoot A K neg (perm i) (t^exponent i)*
          modelRoot A K neg (perm (perm i)) ((t^exponent i)^exponent (perm i)) := rfl

end SymmetricSubgroupAsymptotics.CFSGSerreTripleFixedRoots
