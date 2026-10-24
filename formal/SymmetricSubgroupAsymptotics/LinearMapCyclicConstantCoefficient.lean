import SymmetricSubgroupAsymptotics.LinearMapPositiveCyclicDecomposition

/-! Invertibility excludes zero constant coefficients in the actual
cyclic polynomial coordinates. The proof uses surjectivity of X on the
literal quotient, without a Jordan-form assumption. -/
set_option autoImplicit false
noncomputable section
open Polynomial
namespace SymmetricSubgroupAsymptotics.LinearMapCyclicConstantCoefficient
variable {K : Type*} [Field K]

theorem constantCoeff_ne_zero_of_X_smul_surjective (p : K[X])
    (hX : Function.Surjective (fun v : K[X] ⧸ Submodule.span K[X] ({p} : Set K[X]) =>
      (X : K[X]) • v)) : p.coeff 0 ≠ 0 := by
  intro hp
  let I := Submodule.span K[X] ({p} : Set K[X])
  obtain ⟨v, hv⟩ := hX (I.mkQ 1)
  obtain ⟨f, rfl⟩ := I.mkQ_surjective v
  have hv' : I.mkQ (X*f) = I.mkQ 1 := hv
  have hz : I.mkQ (X*f-1) = 0 := by rw [map_sub, hv', sub_self]
  have hd : p ∣ X*f-1 := Ideal.mem_span_singleton.mp ((Submodule.Quotient.mk_eq_zero I).mp hz)
  obtain ⟨g, hg⟩ := hd
  have h := congrArg (fun q : K[X] => q.eval 0) hg
  simp [← coeff_zero_eq_eval_zero, hp] at h

theorem constantCoeff_ne_zero {V : Type*} [AddCommGroup V] [Module K V]
    [Module.Finite K V] {A : Module.End K V}
    (C : LinearMapPositiveCyclicDecomposition.Chart A) (hA : Function.Surjective A) (i : C.ι) :
    (C.polynomial i).coeff 0 ≠ 0 := by
  classical
  have hs : Function.Surjective (fun v : Module.AEval' A => (X : K[X]) • v) := by
    intro v
    obtain ⟨w, hw⟩ := hA ((Module.AEval'.of A).symm v)
    refine ⟨Module.AEval'.of A w, ?_⟩
    apply (Module.AEval'.of A).symm.injective
    simpa only [Module.AEval.of_symm_X_smul, LinearEquiv.symm_apply_apply] using hw
  have hq : Function.Surjective (fun v : K[X] ⧸ Submodule.span K[X] ({C.polynomial i} : Set K[X]) =>
      (X : K[X]) • v) := by
    intro v
    let z : (j : C.ι) → K[X] ⧸ Submodule.span K[X] ({C.polynomial j} : Set K[X]) :=
      Pi.single i v
    obtain ⟨w, hw⟩ := hs (C.equiv.symm z)
    refine ⟨C.equiv w i, ?_⟩
    have h := congrFun (congrArg C.equiv hw) i
    simpa only [map_smul, LinearEquiv.apply_symm_apply, z, Pi.single_eq_same] using h
  exact constantCoeff_ne_zero_of_X_smul_surjective (C.polynomial i) hq

end SymmetricSubgroupAsymptotics.LinearMapCyclicConstantCoefficient
