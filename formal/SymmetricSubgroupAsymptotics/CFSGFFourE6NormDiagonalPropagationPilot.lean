import SymmetricSubgroupAsymptotics.CFSGFFourE6NormSimpleCoefficientPilot

/-! A selected 26-edge forest propagates fixed diagonal entries from the
52 norm-pair coordinates. Every edge is an actual coefficient-one E-step
with zero divided-square coefficient. No general Roots Fintype is reduced. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NormDiagonalPropagationPilot
open CFSGFFourE6NormPairRepresentatives CFSGFFourE6NormQuotientCoefficientPilot
open CFSGIntegerMatrixPairing
local instance : Fintype PairIndex := by unfold PairIndex;infer_instance
local instance : DecidableEq PairIndex := by unfold PairIndex;infer_instance

structure Step where
  child : RawIndex
  parent : RawIndex
  node : Fin 6
  reversed : Bool
  rank : ℕ
  deriving DecidableEq

def steps : Finset Step := {
    ⟨.inl 1,.inr ![0,0,0,1,0,0],3,true,2⟩,
    ⟨.inl 3,.inr ![0,0,0,0,1,0],4,true,1⟩,
    ⟨.inr ![-1,-2,-2,-3,-2,-1],.inr ![-1,-1,-2,-3,-2,-1],1,true,3⟩,
    ⟨.inr ![-1,-1,-2,-3,-2,-1],.inr ![-1,-1,-2,-2,-2,-1],3,true,2⟩,
    ⟨.inr ![-1,-1,-2,-2,-2,-1],.inr ![-1,-1,-2,-2,-1,-1],4,true,1⟩,
    ⟨.inr ![-1,-1,-1,-2,-1,-1],.inr ![-1,-1,-2,-2,-1,-1],2,false,1⟩,
    ⟨.inr ![-1,-1,-1,-1,-1,-1],.inr ![-1,-1,-1,-1,-1,0],5,true,1⟩,
    ⟨.inr ![-1,0,-1,-1,-1,-1],.inr ![-1,0,-1,-1,-1,0],5,true,1⟩,
    ⟨.inr ![0,-1,-1,-2,-1,0],.inr ![-1,-1,-1,-2,-1,0],0,false,1⟩,
    ⟨.inr ![0,-1,-1,-1,-1,0],.inr ![-1,-1,-1,-1,-1,0],0,false,1⟩,
    ⟨.inr ![0,-1,0,-1,0,0],.inr ![0,-1,-1,-1,0,0],2,false,1⟩,
    ⟨.inr ![0,-1,0,0,0,0],.inr ![0,-1,0,-1,0,0],3,false,2⟩,
    ⟨.inr ![0,0,-1,-1,-1,0],.inr ![-1,0,-1,-1,-1,0],0,false,1⟩,
    ⟨.inr ![0,0,0,-1,0,0],.inr ![0,0,-1,-1,0,0],2,false,1⟩,
    ⟨.inr ![0,0,0,1,0,0],.inl 2,3,false,1⟩,
    ⟨.inr ![0,0,1,1,1,0],.inr ![0,0,0,1,1,0],2,false,1⟩,
    ⟨.inr ![0,1,0,0,0,0],.inl 3,1,false,2⟩,
    ⟨.inr ![0,1,0,1,0,0],.inr ![0,1,0,1,1,0],4,true,1⟩,
    ⟨.inr ![0,1,1,1,1,0],.inr ![0,1,0,1,1,0],2,false,1⟩,
    ⟨.inr ![0,1,1,2,1,0],.inr ![0,1,1,2,1,1],5,true,1⟩,
    ⟨.inr ![1,0,1,1,1,1],.inr ![0,0,1,1,1,1],0,false,1⟩,
    ⟨.inr ![1,1,1,1,1,1],.inr ![0,1,1,1,1,1],0,false,1⟩,
    ⟨.inr ![1,1,1,2,1,1],.inr ![0,1,1,2,1,1],0,false,1⟩,
    ⟨.inr ![1,1,2,2,2,1],.inr ![1,1,1,2,2,1],2,false,1⟩,
    ⟨.inr ![1,1,2,3,2,1],.inr ![1,1,2,2,2,1],3,false,2⟩,
    ⟨.inr ![1,2,2,3,2,1],.inr ![1,1,2,3,2,1],1,false,3⟩}

def row (s:Step) : RawIndex := if s.reversed then s.parent else s.child
def col (s:Step) : RawIndex := if s.reversed then s.child else s.parent

def rawNorm : RawIndex→ℤ
  | .inl _=>2
  | .inr v=>integerPairing CartanMatrix.E₆ v v

theorem steps_entries : ∀s∈steps,s.child≠s.parent ∧
    rawNorm s.child=2 ∧ rawNorm s.parent=2 ∧
    stepEntry s.node (row s) (col s)%2=1 ∧ secondEntry s.node (row s) (col s)%2=0 :=
  by decide +kernel

theorem steps_cover : ∀j:PairIndex,∃s∈steps,s.child=fixedIndex j := by decide +kernel

theorem steps_parent : ∀s∈steps,
    (∃k:PairIndex,s.parent=normIndex k ∨ s.parent=partnerIndex (normIndex k)) ∨
      (∃t∈steps,t.child=s.parent ∧ t.rank<s.rank) := by decide +kernel

theorem fixed_values_of_steps {T:Type*} [One T] (f:RawIndex→T)
    (hnorm:∀k:PairIndex,f (normIndex k)=1 ∧ f (partnerIndex (normIndex k))=1)
    (hedge:∀s∈steps,f s.child=f s.parent) : ∀j:PairIndex,f (fixedIndex j)=1 := by
  have hsteps:∀n:ℕ,∀s∈steps,s.rank=n→f s.child=1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih=>
      intro s hs hsn
      rw [hedge s hs]
      rcases steps_parent s hs with hknown|hparent
      · obtain ⟨k,hk|hk⟩:=hknown
        · rw [hk]
          exact (hnorm k).1
        · rw [hk]
          exact (hnorm k).2
      · obtain ⟨t,ht,hchild,hlt⟩:=hparent
        rw [←hchild]
        exact ih t.rank (by simpa only [hsn] using hlt) t ht rfl
  intro j
  obtain ⟨s,hs,hchild⟩:=steps_cover j
  rw [←hchild]
  exact hsteps s.rank s hs rfl

end SymmetricSubgroupAsymptotics.CFSGFFourE6NormDiagonalPropagationPilot
