import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumnCertificate
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleWeylColumnAction

/-! One actual-action installer for arbitrary sparse column certificates.
The same checked root words and original parameter-preserving equivalence
are retained. Supplying all 26 kernel certificates, not a single column,
is necessary before invoking action faithfulness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumnInstaller
open CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
open CFSGFFourE6MiddleWeylCoordinateSteps CFSGFFourE6MiddleWeylColumnPilot
open CFSGFFourE6MiddleWeylColumnAction CFSGFFourE6MiddleWeylColumnCertificate
open CFSGFFourE6CharacteristicTwoNormImage
open CFSGFFourOriginalMiddleWeylColumnAction CFSGFFourOriginalFoldedEquivalence

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

private theorem finite_action_endpoint {G V : Type*} [Monoid G]
    (act : G→V→V) (hone : ∀x,act 1 x=x)
    (hmul : ∀g h x,act (g*h) x=act g (act h x))
    (N : ℕ) (g : Fin N→G) (v : Fin (N+1)→V) (z y : V)
    (hstart : v 0=z) (hend : v (Fin.last N)=y)
    (hstep : ∀i,act (g i) (v i.castSucc)=v i.succ) :
    act (actionWord g) z=y := by
  have h := finite_action_path act hone hmul N g v hstep
  exact (congrArg (act (actionWord g)) hstart.symm).trans (h.trans hend)


private theorem left_axes : ∀n : Fin 12,(leftActions n).2=1∨(leftActions n).2=2 := by decide +kernel
private theorem right_axes : ∀n : Fin 56,(rightActions n).2=1∨(rightActions n).2=2 := by decide +kernel

private theorem support_singleton (K : Type) [Field K] (k : Fin 26) :
    supportVector K {k}=Pi.single k 1 := by
  funext j
  simp only [supportVector,Finset.mem_singleton,Pi.single_apply]

theorem word_column_eq_of_certificate (K : Type) [Field K] [CharP K 2]
    (k : Fin 26) (cert : ColumnCertificate k) :
    matrixAction K (leftWord K)*ᵥ(Pi.single k (1:K))=
      matrixAction K (rightWord K)*ᵥ(Pi.single k (1:K)) := by
  have hleft : matrixAction K (leftWord K)*ᵥ(Pi.single k (1:K))=
      supportVector K (cert.leftStates (Fin.last 12)) :=
    finite_action_endpoint
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
      (fun n=>supportVector K (cert.leftStates n)) (Pi.single k 1)
      (supportVector K (cert.leftStates (Fin.last 12)))
      ((congrArg (supportVector K) cert.leftInitial).trans (support_singleton K k))
      rfl
      (fun i=>support_transition K _ _ (left_axes i) _ _ (cert.leftTransition i))
  have hright : matrixAction K (rightWord K)*ᵥ(Pi.single k (1:K))=
      supportVector K (cert.leftStates (Fin.last 12)) :=
    finite_action_endpoint
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
      (fun n=>supportVector K (cert.rightStates n)) (Pi.single k 1)
      (supportVector K (cert.leftStates (Fin.last 12)))
      ((congrArg (supportVector K) cert.rightInitial).trans (support_singleton K k))
      (congrArg (supportVector K) cert.finalAgreement.symm)
      (fun i=>support_transition K _ _ (right_axes i) _ _ (cert.rightTransition i))
  exact hleft.trans hright.symm

theorem original_word_column_eq_of_certificate (K : Type) [Field K] [Finite K] [CharP K 2]
    (k : Fin 26) (cert : ColumnCertificate k) :
    matrixAction K (modelEquivFolded K (originalLeftWord K))*ᵥ(Pi.single k (1:K))=
      matrixAction K (modelEquivFolded K (originalRightWord K))*ᵥ(Pi.single k (1:K)) := by
  rw [modelEquivFolded_leftWord,modelEquivFolded_rightWord]
  exact word_column_eq_of_certificate K k cert

end SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumnInstaller
