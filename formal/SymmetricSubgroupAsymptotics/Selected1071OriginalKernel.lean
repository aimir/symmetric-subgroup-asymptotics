import SymmetricSubgroupAsymptotics.Selected1071QuotientGraphData
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! The four displayed kernel elements are an actual central subgroup of
exactly the original generated sixteen-point group. Membership is witnessed
by the stored signed original words, without an enumeration of that group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1071QuotientGraph

def Original : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range sourceGenerators)

def source (j : Fin 4) : Original :=
  ⟨sourceGenerators j,Subgroup.subset_closure ⟨j,rfl⟩⟩

private theorem signed_mem (j : Fin 8) : signedSource j ∈ Original := by
  unfold signedSource
  split
  · exact (source _).property
  · exact Original.inv_mem (source _).property

theorem kernel_mem_original (i : Fin 4) : kernelElements i ∈ Original := by
  have hw : kernelWordElement i ∈ Original := by
    apply Original.list_prod_mem
    intro p hp
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hp
    exact signed_mem j
  have he : kernelWordElement i=kernelElements i := by
    apply Equiv.ext
    intro x
    exact kernelWord_checked i x
  exact he ▸ hw

private def kernelMul (i j : Fin 4) : Fin 4 :=
  (((#[#[0,1,2,3],#[1,0,3,2],#[2,3,0,1],#[3,2,1,0]] :
    Array (Array (Fin 4)))[i.val]!)[j.val]!)

private theorem kernel_mul : ∀ (i j : Fin 4) (x : Fin 16),
    (kernelElements i*kernelElements j) x=kernelElements (kernelMul i j) x := by
  decide +kernel

private theorem kernel_inv : ∀ (i : Fin 4) (x : Fin 16),
    (kernelElements i)⁻¹ x=kernelElements i x := by decide +kernel

def originalKernel : Subgroup Original where
  carrier := {g | ∃ i : Fin 4, g.val=kernelElements i}
  one_mem' := ⟨0,by ext x; revert x; decide +kernel⟩
  mul_mem' := by
    rintro a b ⟨i,hi⟩ ⟨j,hj⟩
    refine ⟨kernelMul i j,?_⟩
    change a.val*b.val=kernelElements (kernelMul i j)
    rw [hi,hj]
    apply Equiv.ext
    intro x
    exact kernel_mul i j x
  inv_mem' := by
    rintro a ⟨i,hi⟩
    refine ⟨i,?_⟩
    change a.val⁻¹=kernelElements i
    rw [hi]
    apply Equiv.ext
    intro x
    exact kernel_inv i x

theorem kernel_central (i : Fin 4) (g : Original) :
    kernelElements i*g.val=g.val*kernelElements i := by
  have hle : Original ≤ Subgroup.centralizer {kernelElements i} := by
    apply (Subgroup.closure_le _).mpr
    rintro p ⟨j,rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply Equiv.ext
    intro x
    exact (kernel_central_generators i j x).symm
  have hg := hle g.property
  exact (Subgroup.mem_centralizer_singleton_iff.mp hg).symm

instance : originalKernel.Normal where
  conj_mem := by
    rintro n ⟨i,hi⟩ g
    refine ⟨i,?_⟩
    change g.val*n.val*g.val⁻¹=kernelElements i
    rw [hi,← kernel_central i g,mul_inv_cancel_right]

/-- This is the literal original denominator, before any target graph map. -/
def kernelElement (i : Fin 4) : originalKernel :=
  ⟨⟨kernelElements i,kernel_mem_original i⟩,i,rfl⟩

theorem kernelElement_surjective : Function.Surjective kernelElement := by
  rintro ⟨g,i,hi⟩
  refine ⟨i,?_⟩
  apply Subtype.ext
  exact Subtype.ext hi.symm

end SymmetricSubgroupAsymptotics.Selected1071QuotientGraph
