import Mathlib.Algebra.Module.PID
import Mathlib.LinearAlgebra.AnnihilatingPolynomial

/-! A finite-dimensional endomorphism has one actual vector whose
annihilating polynomials are exactly the annihilating polynomials of the
whole endomorphism. This uses the PID module theorem over `K[X]`, and
therefore holds over every field, including finite fields. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.LinearMapMaximalAnnihilatorVector

open Polynomial
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V]

set_option backward.isDefEq.respectTransparency false in
theorem exists_vector (A : Module.End K V) :
    ∃ v : V, ∀ p : K[X], (aeval A p) v = 0 ↔ aeval A p = 0 := by
  letI : Module K[X] (Module.AEval' A) :=
    Module.AEval.instModulePolynomial (R := K) (M := V) A
  obtain ⟨v, hv⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator
    (R := K[X]) (M := Module.AEval' A)
  refine ⟨(Module.AEval'.of A).symm v, fun p => ?_⟩
  have hp : p ∈ LinearMap.ker (LinearMap.toSpanSingleton K[X] (Module.AEval' A) v) ↔
      p ∈ RingHom.ker (aeval A) := by
    rw [hv, Module.AEval.annihilator_eq_ker_aeval]
  change (p • v : Module.AEval' A) = 0 ↔ aeval A p = 0
  simpa only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply,
    RingHom.mem_ker] using hp

end SymmetricSubgroupAsymptotics.LinearMapMaximalAnnihilatorVector
