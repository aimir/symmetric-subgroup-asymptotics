import SymmetricSubgroupAsymptotics.CFSGSerreModelRootGeneration
import Mathlib.GroupTheory.Commutator.Basic

/-! Literal fixed-root witnesses in the original generated twist graph.
This is membership in the fixed subgroup only: membership in its derived
subgroup must be proved separately by actual commutator words. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGSerreFixedRootElements
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence CFSGSerreModelRootGeneration
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (K : Type) [Field K]
    (perm : Fin n→Fin n) (exponent : Fin n→ℕ)

theorem root_mem_fixed (neg : Bool) (i : Fin n) (t : K)
    (hi : perm i=i) (ht : t^exponent i=t) :
    (modelRoot A K neg i t).val∈fixedSubgroup A K perm exponent := by
  refine ⟨(modelRoot A K neg i t).property,?_⟩
  change ((modelRoot A K neg i t).val,(modelRoot A K neg i t).val)∈
    twistGraph A K perm exponent
  apply Subgroup.subset_closure
  refine ⟨neg,i,t,rfl,?_⟩
  rw [hi,ht]
  rfl

def fixedRoot (neg : Bool) (i : Fin n) (t : K)
    (hi : perm i=i) (ht : t^exponent i=t) : fixedSubgroup A K perm exponent :=
  ⟨(modelRoot A K neg i t).val,root_mem_fixed A K perm exponent neg i t hi ht⟩

def fixedToModel : fixedSubgroup A K perm exponent→*Model A K where
  toFun g := ⟨g.val,g.property.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem fixedToModel_root (neg : Bool) (i : Fin n) (t : K)
    (hi : perm i=i) (ht : t^exponent i=t) :
    fixedToModel A K perm exponent (fixedRoot A K perm exponent neg i t hi ht)=
      modelRoot A K neg i t := rfl

def derivedToModel : commutator (fixedSubgroup A K perm exponent)→*Model A K :=
  (fixedToModel A K perm exponent).comp (commutator (fixedSubgroup A K perm exponent)).subtype

def derivedCommutator (g h : fixedSubgroup A K perm exponent) :
    commutator (fixedSubgroup A K perm exponent) :=
  ⟨⁅g,h⁆,by rw [commutator_eq_closure];exact Subgroup.subset_closure (commutator_mem_commutatorSet g h)⟩

@[simp] theorem derivedToModel_commutator (g h : fixedSubgroup A K perm exponent) :
    derivedToModel A K perm exponent (derivedCommutator A K perm exponent g h)=
      ⁅fixedToModel A K perm exponent g,fixedToModel A K perm exponent h⁆ := by
  exact map_commutatorElement (fixedToModel A K perm exponent) g h

end SymmetricSubgroupAsymptotics.CFSGSerreFixedRootElements
