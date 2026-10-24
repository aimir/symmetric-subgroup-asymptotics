import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleScalarPolynomialData
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylCoordinateSteps
import SymmetricSubgroupAsymptotics.CFSGSparseBivariateListEvaluation
import Mathlib.Tactic.Ring

/-! Finite parity-count transitions evaluate in the SAME actual signed
norm26 action. No noncomputable polynomial multiplication is reduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6MiddlePolynomialTransition
open CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
open CFSGFFourE6MiddleParameterMatrixEntries CFSGFFourE6MiddleScalarPolynomialData
open CFSGFFourE6MiddleWeylCoordinateSteps CFSGFFourE6MiddleWeylBasisLabels
open CFSGFFourE6NormMatrixAction CFSGFFourE6CharacteristicTwoNormImage
open CFSGSparseBivariateListEvaluation
variable (K : Type) [Field K] [CharP K 2]

private theorem zmod_val_cast (n : ℤ) : (((n : ZMod 2).val : ℕ) : K)=(n : K) := by
  have he := congrArg (ZMod.castHom (dvd_refl 2) K) (ZMod.natCast_zmod_val (n : ZMod 2))
  simpa only [map_natCast,map_intCast] using he

omit [CharP K 2] in
private theorem monomial_twice (c d : K) (p : Exponent) :
    monomialValue c d (2*p.1,2*p.2)=(monomialValue c d p)^2 := by
  simp only [monomialValue]
  rw [Nat.mul_comm 2 p.1,Nat.mul_comm 2 p.2,pow_mul,pow_mul,mul_pow]

private theorem parameterEntry_coefficients (a : Action) (t : K) (j k : Fin 26) :
    parameterEntry a.1.1 a.1.2 t j k=(if j=k then 1 else 0)+
      t*((linearCoefficient a j k).val : K)+t^2*((quadraticCoefficient a j k).val : K) := by
  simp only [parameterEntry,linearCoefficient,quadraticCoefficient,zmod_val_cast]

def evaluatedVector (c d : K) (v : Fin 26→List Exponent) : Fin 26→K :=
  fun j=>evaluate c d (v j)

private theorem evaluate_stepContributions (c d : K) (a : Action)
    (v : Fin 26→List Exponent) (j : Fin 26) :
    evaluate c d (stepContributions a v j)=evaluate c d (v j)+
      ∑k : Fin 26, (((linearCoefficient a j k).val : K)*monomialValue c d a.2*evaluate c d (v k)+
        ((quadraticCoefficient a j k).val : K)*(monomialValue c d a.2)^2*evaluate c d (v k)) := by
  rw [stepContributions,evaluate_append,evaluate_flatMap,←Fin.sum_univ_def]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [evaluate_append]
  have hs (p : Exponent) : evaluate c d (shift p (v k))=
      monomialValue c d p*evaluate c d (v k) := evaluate_shift c d p (v k)
  simp only [scaledShift,evaluate_replicate_flatten]
  rw [hs a.2,hs (2*a.2.1,2*a.2.2),monomial_twice]
  simp only [mul_assoc]

theorem polynomial_transition_action (c d : K) (a : Action) (ha : a.1.2=1∨a.1.2=2)
    (v w : Fin 26→List Exponent) (hstep : parityTransition a v w) :
    matrixAction K (foldedRoot K a.1.1 a.1.2 (monomialValue c d a.2))*ᵥevaluatedVector K c d v=
      evaluatedVector K c d w := by
  have hentry (j k : Fin 26) :
      matrixAction K (foldedRoot K a.1.1 a.1.2 (monomialValue c d a.2)) j k=
        parameterEntry a.1.1 a.1.2 (monomialValue c d a.2) j k :=
    normMatrixAction_middle_parameter_entry K a.1.1 a.1.2 ha _ j k
  funext j
  have hid : (∑k : Fin 26,(if j=k then (1:K) else 0)*evaluate c d (v k))=
      evaluate c d (v j) := by
    calc
      _=(if j=j then (1:K) else 0)*evaluate c d (v j) :=
        Finset.sum_eq_single j
          (fun k _ hk=>by rw [if_neg (Ne.symm hk),zero_mul])
          (fun hj=>False.elim (hj (Finset.mem_univ j)))
      _=evaluate c d (v j) := by simp only [if_true,one_mul]
  change (∑k : Fin 26,matrixAction K
    (foldedRoot K a.1.1 a.1.2 (monomialValue c d a.2)) j k*evaluate c d (v k))=
      evaluate c d (w j)
  calc
    _=(∑k : Fin 26,(if j=k then (1:K) else 0)*evaluate c d (v k))+
        ∑k : Fin 26, (((linearCoefficient a j k).val : K)*monomialValue c d a.2*evaluate c d (v k)+
          ((quadraticCoefficient a j k).val : K)*(monomialValue c d a.2)^2*evaluate c d (v k)) := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [hentry,parameterEntry_coefficients]
      ring
    _=evaluate c d (stepContributions a v j) := by
      rw [hid,evaluate_stepContributions]
    _=evaluate c d (w j) := evaluate_eq_of_parity c d _ _ (hstep j)

end SymmetricSubgroupAsymptotics.CFSGFFourE6MiddlePolynomialTransition
