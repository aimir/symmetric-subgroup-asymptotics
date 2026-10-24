import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylCoordinateSteps
import SymmetricSubgroupAsymptotics.CFSGFiniteActionPathCertificate
import Mathlib.Data.List.OfFn

/-! The selected sparse certificates evaluate ONE column of two actual
root products in the same folded F4 group. Other columns, and therefore
whole-word equality, remain separate obligations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumnAction
open CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
open CFSGFFourE6MiddleWeylCoordinateSteps CFSGFFourE6MiddleWeylColumnPilot
open CFSGFFourE6CharacteristicTwoNormImage

def actionWord {G : Type*} [Monoid G] {N : ℕ} (g : Fin N→G) : G :=
  (List.ofFn g).reverse.prod

private theorem finite_action_path {G V : Type*} [Monoid G]
    (act : G→V→V) (hone : ∀x,act 1 x=x)
    (hmul : ∀g h x,act (g*h) x=act g (act h x))
    (N : ℕ) (g : Fin N→G) (v : Fin (N+1)→V)
    (hstep : ∀i,act (g i) (v i.castSucc)=v i.succ) :
    act (List.ofFn g).reverse.prod (v 0)=v (Fin.last N) := by
  induction N with
  | zero =>
    simp only [List.ofFn_zero,List.reverse_nil,List.prod_nil]
    exact hone _
  | succ N ih =>
    rw [List.ofFn_succ,List.reverse_cons,List.prod_append]
    simp only [List.prod_cons,List.prod_nil,mul_one]
    rw [hmul]
    have hz := hstep (0 : Fin (N+1))
    rw [Fin.castSucc_zero] at hz
    rw [hz]
    simpa only [Fin.succ_last] using ih (fun i=>g i.succ) (fun i=>v i.succ)
      (fun i=>by simpa only [Fin.castSucc_succ] using hstep i.succ)

private theorem finite_action_fixed {G V : Type*} [Monoid G]
    (act : G→V→V) (hone : ∀x,act 1 x=x)
    (hmul : ∀g h x,act (g*h) x=act g (act h x))
    (N : ℕ) (g : Fin N→G) (v : Fin (N+1)→V) (z : V)
    (hstart : v 0=z) (hend : v (Fin.last N)=z)
    (hstep : ∀i,act (g i) (v i.castSucc)=v i.succ) :
    act (actionWord g) z=z := by
  have h := finite_action_path act hone hmul N g v hstep
  exact (congrArg (act (actionWord g)) hstart.symm).trans (h.trans hend)

private theorem right_block_transitions (b : Fin 7) (k : Fin 8) : ∀j : Fin 26,
    (∑r ∈ rightSupports (rightBlock b k).castSucc,
      oneEntry (rightActions (rightBlock b k)).1 (rightActions (rightBlock b k)).2 j r)=
      supportValue (rightSupports (rightBlock b k).succ) j := by
  fin_cases b
  · exact right_column_transitions_0 k
  · exact right_column_transitions_1 k
  · exact right_column_transitions_2 k
  · exact right_column_transitions_3 k
  · exact right_column_transitions_4 k
  · exact right_column_transitions_5 k
  · exact right_column_transitions_6 k

private theorem right_transitions (n : Fin 56) : ∀j : Fin 26,
    (∑k ∈ rightSupports n.castSucc,oneEntry (rightActions n).1 (rightActions n).2 j k)=
      supportValue (rightSupports n.succ) j := by
  let b : Fin 7 := ⟨n.val/8,by omega⟩
  let k : Fin 8 := ⟨n.val%8,Nat.mod_lt _ (by decide)⟩
  have he : rightBlock b k=n := by
    apply Fin.ext
    dsimp only [rightBlock,b,k]
    omega
  rw [←he]
  exact right_block_transitions b k

private theorem left_axes : ∀n : Fin 12,(leftActions n).2=1∨(leftActions n).2=2 := by decide +kernel
private theorem right_axes : ∀n : Fin 56,(rightActions n).2=1∨(rightActions n).2=2 := by decide +kernel

variable (K : Type) [Field K] [CharP K 2]

def leftWord : canonicalElementaryGroup realizationData K :=
  actionWord (fun i : Fin 12=>foldedRoot K (leftActions i).1 (leftActions i).2 1)

def rightWord : canonicalElementaryGroup realizationData K :=
  actionWord (fun i : Fin 56=>foldedRoot K (rightActions i).1 (rightActions i).2 1)

omit [CharP K 2] in
private theorem support_singleton : supportVector K {0}=Pi.single 0 1 := by
  funext j
  simp only [supportVector,Finset.mem_singleton,Pi.single_apply]

theorem leftWord_column_zero : matrixAction K (leftWord K)*ᵥ(Pi.single 0 (1:K))=Pi.single 0 1 := by
  have hend : leftSupports (Fin.last 12)={0} := by
    change leftSupports (12 : Fin 13)={0}
    exact initial_and_final_supports.2.2.1
  have hstart : supportVector K (leftSupports 0)=Pi.single 0 1 :=
    (congrArg (supportVector K) initial_and_final_supports.1).trans (support_singleton K)
  have hfinal : supportVector K (leftSupports (Fin.last 12))=Pi.single 0 1 :=
    (congrArg (supportVector K) hend).trans (support_singleton K)
  exact finite_action_fixed
    (fun g : canonicalElementaryGroup realizationData K=>fun x : Fin 26→K=>matrixAction K g*ᵥx)
    (by
      intro x
      change matrixAction K 1*ᵥx=x
      rw [map_one,Matrix.one_mulVec])
    (by
      intro g h x
      change matrixAction K (g*h)*ᵥx=matrixAction K g*ᵥ(matrixAction K h*ᵥx)
      rw [map_mul,Matrix.mulVec_mulVec])
    12 (fun i=>foldedRoot K (leftActions i).1 (leftActions i).2 1)
    (fun n=>supportVector K (leftSupports n)) (Pi.single 0 1) hstart hfinal
    (fun i=>support_transition K _ _ (left_axes i) _ _ (left_column_transitions i))

theorem rightWord_column_zero : matrixAction K (rightWord K)*ᵥ(Pi.single 0 (1:K))=Pi.single 0 1 := by
  have hend : rightSupports (Fin.last 56)={0} := by
    change rightSupports (56 : Fin 57)={0}
    exact initial_and_final_supports.2.2.2
  have hstart : supportVector K (rightSupports 0)=Pi.single 0 1 :=
    (congrArg (supportVector K) initial_and_final_supports.2.1).trans (support_singleton K)
  have hfinal : supportVector K (rightSupports (Fin.last 56))=Pi.single 0 1 :=
    (congrArg (supportVector K) hend).trans (support_singleton K)
  exact finite_action_fixed
    (fun g : canonicalElementaryGroup realizationData K=>fun x : Fin 26→K=>matrixAction K g*ᵥx)
    (by
      intro x
      change matrixAction K 1*ᵥx=x
      rw [map_one,Matrix.one_mulVec])
    (by
      intro g h x
      change matrixAction K (g*h)*ᵥx=matrixAction K g*ᵥ(matrixAction K h*ᵥx)
      rw [map_mul,Matrix.mulVec_mulVec])
    56 (fun i=>foldedRoot K (rightActions i).1 (rightActions i).2 1)
    (fun n=>supportVector K (rightSupports n)) (Pi.single 0 1) hstart hfinal
    (fun i=>support_transition K _ _ (right_axes i) _ _ (right_transitions i))

theorem selected_middle_word_column :
    matrixAction K (leftWord K)*ᵥ(Pi.single 0 (1:K))=
      matrixAction K (rightWord K)*ᵥ(Pi.single 0 (1:K)) :=
  (leftWord_column_zero K).trans (rightWord_column_zero K).symm

end SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumnAction
