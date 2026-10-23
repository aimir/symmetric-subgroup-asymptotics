import SymmetricSubgroupAsymptotics.CFSGGTwoPositiveRootMatrices
import SymmetricSubgroupAsymptotics.CFSGGTwoShortRootVectorActions
import SymmetricSubgroupAsymptotics.CFSGGTwoLongRootVectorActions

/-! Sparse actions of the six actual positive-root polynomials on an
arbitrary vector. Direct finite matches avoid nested vector-literal
reduction in later collecting proofs. Only eight coordinate formulas
are checked for each root, and no field elements are enumerated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoPositiveWordActions
open CFSGGTwoSerreMatrices CFSGGTwoPositiveRootMatrices
open CFSGGTwoOriginalBasisMatrixPilot CFSGGTwoOriginalBasisMatrices
variable (R : Type*) [CommRing R]

def action0 (t : R) (v : Index → R) : Index → R :=
  Sum.elim
    (fun i => match i.val with
      | 0 => v (pos 0)+t*v (pos 1)
      | 1 => v (pos 1)
      | 2 => v (pos 2)+t*(v (pos 3)+v (neg 3))-t^2*v (neg 2)
      | _ => v (pos 3)-t*v (neg 2))
    (fun i => match i.val with
      | 0 => v (neg 0)
      | 1 => v (neg 1)-t*v (neg 0)
      | 2 => v (neg 2)
      | _ => v (neg 3)-t*v (neg 2))

def action1 (t : R) (v : Index → R) : Index → R :=
  Sum.elim
    (fun i => match i.val with
      | 0 => v (pos 0)
      | 1 => v (pos 1)+t*v (pos 2)
      | 2 => v (pos 2)
      | _ => v (pos 3))
    (fun i => match i.val with
      | 0 => v (neg 0)
      | 1 => v (neg 1)
      | 2 => v (neg 2)-t*v (neg 1)
      | _ => v (neg 3))

def action2 (t : R) (v : Index → R) : Index → R :=
  Sum.elim
    (fun i => match i.val with
      | 0 => v (pos 0)+t*v (pos 2)
      | 1 => v (pos 1)-t*(v (pos 3)+v (neg 3))-t^2*v (neg 1)
      | 2 => v (pos 2)
      | _ => v (pos 3)+t*v (neg 1))
    (fun i => match i.val with
      | 0 => v (neg 0)
      | 1 => v (neg 1)
      | 2 => v (neg 2)-t*v (neg 0)
      | _ => v (neg 3)+t*v (neg 1))

def action3 (t : R) (v : Index → R) : Index → R :=
  Sum.elim
    (fun i => match i.val with
      | 0 => v (pos 0)+t*(v (pos 3)+v (neg 3))-t^2*v (neg 0)
      | 1 => v (pos 1)+t*v (neg 2)
      | 2 => v (pos 2)-t*v (neg 1)
      | _ => v (pos 3)-t*v (neg 0))
    (fun i => match i.val with
      | 0 => v (neg 0)
      | 1 => v (neg 1)
      | 2 => v (neg 2)
      | _ => v (neg 3)-t*v (neg 0))

def action4 (t : R) (v : Index → R) : Index → R :=
  Sum.elim
    (fun i => match i.val with
      | 0 => v (pos 0)-t*v (neg 2)
      | 1 => v (pos 1)
      | 2 => v (pos 2)+t*v (neg 0)
      | _ => v (pos 3))
    (fun i => match i.val with
      | 0 => v (neg 0)
      | 1 => v (neg 1)
      | 2 => v (neg 2)
      | _ => v (neg 3))

def action5 (t : R) (v : Index → R) : Index → R :=
  Sum.elim
    (fun i => match i.val with
      | 0 => v (pos 0)+t*v (neg 1)
      | 1 => v (pos 1)-t*v (neg 0)
      | 2 => v (pos 2)
      | _ => v (pos 3))
    (fun i => match i.val with
      | 0 => v (neg 0)
      | 1 => v (neg 1)
      | 2 => v (neg 2)
      | _ => v (neg 3))

def positiveAction (j : Fin 6) (t : R) (v : Index → R) : Index → R :=
  match j.val with
  | 0 => action0 R t v
  | 1 => action1 R t v
  | 2 => action2 R t v
  | 3 => action3 R t v
  | 4 => action4 R t v
  | _ => action5 R t v

theorem positiveAction_0 (t : R) (v : Index → R) :
    positiveAction R 0 t v=action0 R t v := rfl

theorem positiveAction_1 (t : R) (v : Index → R) :
    positiveAction R 1 t v=action1 R t v := rfl

theorem positiveAction_2 (t : R) (v : Index → R) :
    positiveAction R 2 t v=action2 R t v := rfl

theorem positiveAction_3 (t : R) (v : Index → R) :
    positiveAction R 3 t v=action3 R t v := rfl

theorem positiveAction_4 (t : R) (v : Index → R) :
    positiveAction R 4 t v=action4 R t v := rfl

theorem positiveAction_5 (t : R) (v : Index → R) :
    positiveAction R 5 t v=action5 R t v := rfl

private theorem action_0 (t : R) (v : Index → R) :
    polynomialRoot R 0 t *ᵥ v=positiveAction R 0 t v := by
  change (rootTransvection R false 0 t : Mat R) *ᵥ v=action0 R t v
  rw [CFSGGTwoShortRootVectorActions.positive_apply]
  funext x
  rcases x with i|i <;> fin_cases i <;> rfl

private theorem action_1 (t : R) (v : Index → R) :
    polynomialRoot R 1 t *ᵥ v=positiveAction R 1 t v := by
  change (rootTransvection R false 1 t : Mat R) *ᵥ v=action1 R t v
  rw [CFSGGTwoLongRootVectorActions.positive_apply]
  funext x
  rcases x with i|i <;> fin_cases i <;> rfl

private theorem action_2 (t : R) (v : Index → R) :
    polynomialRoot R 2 t *ᵥ v=positiveAction R 2 t v := by
  change (1+t • (firstMatrix R)+t^2 • (Matrix.single (pos 1) (neg 1) (-1:R))) *ᵥ v=action2 R t v
  simp only [firstMatrix,Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,Matrix.single_mulVec]
  funext x
  rcases x with i|i <;> fin_cases i
  · change _ = v (pos 0)+t*v (pos 2)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (pos 1)-t*(v (pos 3)+v (neg 3))-t^2*v (neg 1)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (pos 2)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (pos 3)+t*v (neg 1)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (neg 0)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (neg 1)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (neg 2)-t*v (neg 0)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (neg 3)+t*v (neg 1)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring

private theorem action_3 (t : R) (v : Index → R) :
    polynomialRoot R 3 t *ᵥ v=positiveAction R 3 t v := by
  change (1+t • (-(secondMatrix R))+t^2 • (Matrix.single (pos 0) (neg 0) (-1:R))) *ᵥ v=action3 R t v
  simp only [secondMatrix,Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.neg_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,Matrix.single_mulVec]
  funext x
  rcases x with i|i <;> fin_cases i
  · change _ = v (pos 0)+t*(v (pos 3)+v (neg 3))-t^2*v (neg 0)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (pos 1)+t*v (neg 2)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (pos 2)-t*v (neg 1)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (pos 3)-t*v (neg 0)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (neg 0)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (neg 1)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (neg 2)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (neg 3)-t*v (neg 0)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring

private theorem action_4 (t : R) (v : Index → R) :
    polynomialRoot R 4 t *ᵥ v=positiveAction R 4 t v := by
  change (1+t • (thirdMatrix R)+t^2 • ((0:Mat R))) *ᵥ v=action4 R t v
  simp only [thirdMatrix,Matrix.add_mulVec,Matrix.neg_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,Matrix.single_mulVec,Matrix.zero_mulVec,smul_zero,add_zero]
  funext x
  rcases x with i|i <;> fin_cases i
  · change _ = v (pos 0)-t*v (neg 2)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (pos 1)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (pos 2)+t*v (neg 0)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (pos 3)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (neg 0)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (neg 1)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (neg 2)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (neg 3)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring

private theorem action_5 (t : R) (v : Index → R) :
    polynomialRoot R 5 t *ᵥ v=positiveAction R 5 t v := by
  change (1+t • (-(highestMatrix R))+t^2 • ((0:Mat R))) *ᵥ v=action5 R t v
  simp only [highestMatrix,Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.neg_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,Matrix.single_mulVec,Matrix.zero_mulVec,smul_zero,add_zero]
  funext x
  rcases x with i|i <;> fin_cases i
  · change _ = v (pos 0)+t*v (neg 1)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (pos 1)-t*v (neg 0)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (pos 2)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (pos 3)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (neg 0)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (neg 1)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (neg 2)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring
  · change _ = v (neg 3)
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,pos,neg,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
    simp [Function.update,Fin.ext_iff] <;> ring

theorem polynomialRoot_apply (j : Fin 6) (t : R) (v : Index → R) :
    polynomialRoot R j t *ᵥ v=positiveAction R j t v := by
  fin_cases j
  · exact action_0 R t v
  · exact action_1 R t v
  · exact action_2 R t v
  · exact action_3 R t v
  · exact action_4 R t v
  · exact action_5 R t v

end SymmetricSubgroupAsymptotics.CFSGGTwoPositiveWordActions
