import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleScalarColumnCertificate
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddlePolynomialTransition
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumnAction

/-! The full finite parity certificate is evaluated on ONE actual norm26
column. This asserts a matrix coefficient, not a source-group relation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleScalarColumnAction
open CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
open CFSGFFourE6CharacteristicTwoNormImage CFSGFFourE6MiddleWeylCoordinateSteps
open CFSGFFourE6MiddleWeylColumnAction CFSGFFourE6MiddleScalarColumnCertificate
open CFSGFFourE6MiddlePolynomialTransition CFSGSparseBivariateListEvaluation

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

variable (K : Type) [Field K] [CharP K 2]

def testedWord (c d : K) : canonicalElementaryGroup realizationData K :=
  actionWord (fun i : Fin 68=>foldedRoot K (actions i).1.1 (actions i).1.2
    (monomialValue c d (actions i).2))

theorem testedWord_entry_thirteen_zero (c d : K) :
    matrixAction K (testedWord K c d) 13 0=c+c^2 := by
  have hstart : evaluatedVector K c d (states 0)=Pi.single 0 (1:K) := by
    funext j
    change evaluate c d (states 0 j)=(Pi.single 0 (1:K) : Fin 26→K) j
    rw [initial]
    by_cases hj : j=0 <;> simp [hj,evaluate,monomialValue,Pi.single_apply,eq_comm]
  have hp := finite_action_path
    (fun g : canonicalElementaryGroup realizationData K=>fun x : Fin 26→K=>matrixAction K g*ᵥx)
    (by
      intro x
      change matrixAction K 1*ᵥx=x
      rw [map_one,Matrix.one_mulVec])
    (by
      intro g h x
      change matrixAction K (g*h)*ᵥx=matrixAction K g*ᵥ(matrixAction K h*ᵥx)
      rw [map_mul,Matrix.mulVec_mulVec])
    68 (fun i=>foldedRoot K (actions i).1.1 (actions i).1.2 (monomialValue c d (actions i).2))
    (fun n=>evaluatedVector K c d (states n))
    (fun i=>polynomial_transition_action K c d (actions i) (actions_axes i) _ _ (transitions i))
  have hcolumn : matrixAction K (testedWord K c d)*ᵥ(Pi.single 0 (1:K))=
      evaluatedVector K c d (states (Fin.last 68)) :=
    (congrArg (fun v : Fin 26→K=>matrixAction K (testedWord K c d)*ᵥv) hstart.symm).trans hp
  calc
    matrixAction K (testedWord K c d) 13 0=
        (matrixAction K (testedWord K c d)*ᵥ(Pi.single 0 (1:K))) 13 := by
      rw [Matrix.mulVec_single_one]
      rfl
    _=evaluatedVector K c d (states (Fin.last 68)) 13 := congrArg (fun v : Fin 26→K=>v 13) hcolumn
    _=c+c^2 := by
      change evaluate c d (states (Fin.last 68) 13)=c+c^2
      rw [final_thirteen]
      simp only [evaluate,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
        monomialValue,pow_one,pow_zero,mul_one,add_zero]

end SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleScalarColumnAction
