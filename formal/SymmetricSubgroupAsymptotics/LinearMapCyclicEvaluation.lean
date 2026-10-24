import SymmetricSubgroupAsymptotics.LinearMapCyclicConstantCoefficient
import SymmetricSubgroupAsymptotics.LinearMapPositivePrimaryDecomposition

/-! Surjectivity of `A-c` excludes the root `c` from every actual cyclic
polynomial and every retained primary factor. The argument evaluates a
literal quotient relation at `c`; no eigenvector normal form is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Polynomial

namespace SymmetricSubgroupAsymptotics.LinearMapCyclicEvaluation
variable {K : Type*} [Field K]

theorem eval_ne_zero_of_linear_smul_surjective (p : K[X]) (c : K)
    (hX : Function.Surjective
      (fun v : K[X] ⧸ Submodule.span K[X] ({p} : Set K[X]) => (X-Polynomial.C c) • v)) :
    p.eval c ≠ 0 := by
  intro hp
  let I := Submodule.span K[X] ({p} : Set K[X])
  obtain ⟨v,hv⟩ := hX (I.mkQ 1)
  obtain ⟨f,rfl⟩ := I.mkQ_surjective v
  have hv' : I.mkQ ((X-Polynomial.C c)*f) = I.mkQ 1 := hv
  have hz : I.mkQ ((X-Polynomial.C c)*f-1) = 0 := by rw [map_sub,hv',sub_self]
  have hd : p ∣ (X-Polynomial.C c)*f-1 :=
    Ideal.mem_span_singleton.mp ((Submodule.Quotient.mk_eq_zero I).mp hz)
  obtain ⟨g,hg⟩ := hd
  have h := congrArg (fun q : K[X] => q.eval c) hg
  simp only [eval_sub,eval_mul,eval_X,eval_C,eval_one,hp,sub_self,
    zero_mul,zero_sub,neg_eq_zero,one_ne_zero] at h

variable {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]

omit [Module.Finite K V] in
theorem eval_ne_zero {A : Module.End K V}
    (C : LinearMapPositiveCyclicDecomposition.Chart A) (c : K)
    (hA : Function.Surjective (A-c • (LinearMap.id : Module.End K V))) (i : C.ι) :
    (C.polynomial i).eval c ≠ 0 := by
  classical
  have hs : Function.Surjective
      (fun v : Module.AEval' A => (X-Polynomial.C c : K[X]) • v) := by
    intro v
    obtain ⟨w,hw⟩ := hA ((Module.AEval'.of A).symm v)
    refine ⟨Module.AEval'.of A w, ?_⟩
    apply (Module.AEval'.of A).symm.injective
    change (Module.AEval'.of A).symm
      ((X-Polynomial.C c : K[X]) • (Module.AEval'.of A w)) = (Module.AEval'.of A).symm v
    rw [Module.AEval.of_symm_smul]
    simpa only [map_sub,aeval_X,aeval_C,Module.End.smul_def,
      LinearEquiv.symm_apply_apply,LinearMap.sub_apply,
      Algebra.algebraMap_eq_smul_one,Module.End.one_apply,LinearMap.smul_apply] using hw
  have hq : Function.Surjective
      (fun v : K[X] ⧸ Submodule.span K[X] ({C.polynomial i} : Set K[X]) =>
        (X-Polynomial.C c) • v) := by
    intro v
    let z : (j : C.ι) → K[X] ⧸ Submodule.span K[X] ({C.polynomial j} : Set K[X]) :=
      Pi.single i v
    obtain ⟨w,hw⟩ := hs (C.equiv.symm z)
    refine ⟨C.equiv w i, ?_⟩
    have h := congrFun (congrArg C.equiv hw) i
    simpa only [map_smul,LinearEquiv.apply_symm_apply,z,Pi.single_eq_same] using h
  exact eval_ne_zero_of_linear_smul_surjective (C.polynomial i) c hq

omit [Module.Finite K V] in
theorem primary_eval_ne_zero {A : Module.End K V}
    (C : LinearMapPositivePrimaryDecomposition.Chart A) (c : K)
    (hA : Function.Surjective (A-c • (LinearMap.id : Module.End K V))) (i : C.cyclic.ι) :
    (C.prime i).eval c ≠ 0 := by
  have h := eval_ne_zero C.cyclic c hA i
  rw [C.power_eq,eval_pow] at h
  intro hz
  exact h (by rw [hz,zero_pow (Nat.ne_of_gt (C.positive i))])

end SymmetricSubgroupAsymptotics.LinearMapCyclicEvaluation
