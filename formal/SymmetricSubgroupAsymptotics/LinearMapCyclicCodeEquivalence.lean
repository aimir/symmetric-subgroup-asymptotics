import SymmetricSubgroupAsymptotics.LinearMapPositiveCyclicDecomposition
import SymmetricSubgroupAsymptotics.FiniteMultisetLabelMatching
import Mathlib.LinearAlgebra.Pi

/-! Equal multisets of actual cyclic polynomial factors give an actual
intertwining linear equivalence. The existential decomposition suffices;
no uniqueness theorem or invariant-factor premise is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.LinearMapCyclicCodeEquivalence
open LinearMapPositiveCyclicDecomposition FiniteMultisetLabelMatching Polynomial
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup W] [Module K W] [Module.Finite K W]

def code {A : Module.End K V} (C : Chart A) : Multiset K[X] := labelMultiset C.polynomial

set_option backward.isDefEq.respectTransparency false in
def moduleEquiv {A : Module.End K V} {B : Module.End K W}
    (C : Chart A) (D : Chart B) (h : code C = code D) :
    Module.AEval' A ≃ₗ[K[X]] Module.AEval' B := by
  classical
  let E : C.ι ≃ D.ι := matchingEquiv C.polynomial D.polynomial h
  have he (i : C.ι) : C.polynomial i = D.polynomial (E i) :=
    (matchingEquiv_spec C.polynomial D.polynomial h i).symm
  let P : ((i : C.ι) → K[X] ⧸ Submodule.span K[X] ({C.polynomial i} : Set K[X])) ≃ₗ[K[X]]
      ((i : C.ι) → K[X] ⧸ Submodule.span K[X] ({D.polynomial (E i)} : Set K[X])) :=
    LinearEquiv.piCongrRight (fun i => Submodule.quotEquivOfEq _ _
      (congrArg (fun p : K[X] => Submodule.span K[X] ({p} : Set K[X])) (he i)))
  exact C.equiv.trans (P.trans ((LinearEquiv.piCongrLeft K[X]
    (fun i : D.ι => K[X] ⧸ Submodule.span K[X] ({D.polynomial i} : Set K[X])) E).trans D.equiv.symm))

theorem exists_intertwining_equiv {A : Module.End K V} {B : Module.End K W}
    (C : Chart A) (D : Chart B) (h : code C = code D) :
    ∃ F : V ≃ₗ[K] W, ∀ v, F (A v) = B (F v) := by
  let E := moduleEquiv C D h
  let F := (Module.AEval'.of A).trans ((E.restrictScalars K).trans (Module.AEval'.of B).symm)
  refine ⟨F, fun v => ?_⟩
  have he := congrArg (Module.AEval'.of B).symm (E.map_smul (Polynomial.X : K[X]) (Module.AEval'.of A v))
  change (Module.AEval'.of B).symm (E (Module.AEval'.of A (A v))) =
    B ((Module.AEval'.of B).symm (E (Module.AEval'.of A v)))
  simpa only [Module.AEval.X_smul_of, Module.AEval.of_symm_X_smul] using he

end SymmetricSubgroupAsymptotics.LinearMapCyclicCodeEquivalence
