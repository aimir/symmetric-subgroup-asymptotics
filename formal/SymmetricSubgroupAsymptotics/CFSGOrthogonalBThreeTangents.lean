import SymmetricSubgroupAsymptotics.CFSGOrthogonalBTangentCount
import SymmetricSubgroupAsymptotics.CFSGThreeSetAvoidance
import Mathlib.Data.Fin.VecNotation

/-! Three original singular tangent hyperplanes do not cover the SAME
singular cone. The common zero vector supplies the strict inequality
even at field order three. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularVectorCount
open CFSGOrthogonalBSerreMatrices CFSGIsometryTangentTransport
variable (K : Type) [Field K] [Finite K]

abbrev Cone (n:ℕ) := {v:Index n→K //(gram K n).toBilin' v v=0}

theorem three_le_card (h2:(2:K)≠0) : 3≤Nat.card K := by
  classical
  have h1:(1:K)≠ -1 := by
    intro h
    apply h2
    calc
      (2:K)=1+1:=by ring
      _=(-1)+1:=congrArg (fun a:K=>a+1) h
      _=0:=neg_add_cancel 1
  let f:Fin 3→K:=![0,1,-1]
  have hf:Function.Injective f:=by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f,Ne.symm h1]
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

private theorem tangent_filter_card [Fintype K] (n:ℕ) (v:Index n→K) :
    (Finset.univ.filter (fun w:Cone K n=>(gram K n).toBilin' v w.val=0)).card=
      Nat.card (Tangent (gram K n).toBilin' v) := by
  classical
  let A:=Finset.univ.filter (fun w:Cone K n=>(gram K n).toBilin' v w.val=0)
  let e:A≃Tangent (gram K n).toBilin' v := {
    toFun:=fun w=>⟨w.val.val,⟨w.val.property,(Finset.mem_filter.mp w.property).2⟩⟩
    invFun:=fun w=>⟨⟨w.val,w.property.1⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,w.property.2⟩⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }
  change A.card=Nat.card (Tangent (gram K n).toBilin' v)
  rw [←Fintype.card_coe A,←Nat.card_eq_fintype_card]
  exact Nat.card_congr e

theorem exists_singular_avoiding_three_tangents (h2:(2:K)≠0) (s:ℕ)
    (v₁ v₂ v₃:Index (s+2)→K) (h₁:v₁≠0) (h₂:v₂≠0) (h₃:v₃≠0)
    (z₁:(gram K (s+2)).toBilin' v₁ v₁=0)
    (z₂:(gram K (s+2)).toBilin' v₂ v₂=0)
    (z₃:(gram K (s+2)).toBilin' v₃ v₃=0) :
    ∃w:Index (s+2)→K,w≠0 ∧ (gram K (s+2)).toBilin' w w=0 ∧
      (gram K (s+2)).toBilin' v₁ w≠0 ∧ (gram K (s+2)).toBilin' v₂ w≠0 ∧
      (gram K (s+2)).toBilin' v₃ w≠0 := by
  classical
  letI:Fintype K:=Fintype.ofFinite K
  let A:=Finset.univ.filter (fun w:Cone K (s+2)=>(gram K (s+2)).toBilin' v₁ w.val=0)
  let B:=Finset.univ.filter (fun w:Cone K (s+2)=>(gram K (s+2)).toBilin' v₂ w.val=0)
  let C:=Finset.univ.filter (fun w:Cone K (s+2)=>(gram K (s+2)).toBilin' v₃ w.val=0)
  let m:=Nat.card K^(2*(s+2)-1)
  have hA:A.card=m := (tangent_filter_card K (s+2) v₁).trans (tangent_card K h2 s v₁ h₁ z₁)
  have hB:B.card=m := (tangent_filter_card K (s+2) v₂).trans (tangent_card K h2 s v₂ h₂ z₂)
  have hC:C.card=m := (tangent_filter_card K (s+2) v₃).trans (tangent_card K h2 s v₃ h₃ z₃)
  let zero:Cone K (s+2):=⟨0,by simp⟩
  have hzeroA:zero∈A:=by simp [A,zero]
  have hzeroB:zero∈B:=by simp [B,zero]
  have hzeroC:zero∈C:=by simp [C,zero]
  have hmass:3*m≤Fintype.card (Cone K (s+2)):=by
    rw [←Nat.card_eq_fintype_card,singular_vectors_card K (s+2) h2]
    have hexp:2*(s+2)=(2*(s+2)-1)+1:=by omega
    rw [hexp,pow_succ]
    exact (Nat.mul_le_mul_right m (three_le_card K h2)).trans_eq (Nat.mul_comm _ _)
  obtain ⟨w,hwA,hwB,hwC⟩:=CFSGThreeSetAvoidance.exists_outside_three A B C zero
    hzeroA hzeroB hzeroC m hA.le hB.le hC.le hmass
  have hn₁:(gram K (s+2)).toBilin' v₁ w.val≠0:=by
    intro h;exact hwA (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  have hn₂:(gram K (s+2)).toBilin' v₂ w.val≠0:=by
    intro h;exact hwB (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  have hn₃:(gram K (s+2)).toBilin' v₃ w.val≠0:=by
    intro h;exact hwC (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  refine ⟨w.val,?_,w.property,hn₁,hn₂,hn₃⟩
  intro hz
  apply hn₁
  rw [hz,map_zero]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularVectorCount
