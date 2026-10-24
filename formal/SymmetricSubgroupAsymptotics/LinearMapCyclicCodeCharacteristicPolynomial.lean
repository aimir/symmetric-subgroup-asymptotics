import SymmetricSubgroupAsymptotics.PolynomialCyclicCharacteristicPolynomial
import SymmetricSubgroupAsymptotics.FiniteIndexedCharacteristicPolynomial
import SymmetricSubgroupAsymptotics.LinearMapCyclicCodeEquivalence

/-! The product of the actual cyclic polynomial labels is the
characteristic polynomial of the original endomorphism. The proof
uses the actual polynomial-module intertwiner and the actual finite
coordinate-product characteristic polynomial, not uniqueness of a
chosen decomposition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.LinearMapCyclicCodeCharacteristicPolynomial
open Polynomial PolynomialCyclicCharacteristicPolynomial
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]

theorem quotient_X_smul (p : K[X])
    (x : K[X] ⧸ Submodule.span K[X] ({p} : Set K[X])) :
    (X : K[X]) • x = rootOperator p x := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro f
  rfl

theorem charpoly_eq_prod {A : Module.End K V}
    (C : LinearMapPositiveCyclicDecomposition.Chart A) :
    A.charpoly = ∏ i : C.ι, C.polynomial i := by
  letI (i : C.ι) : Module.Finite K (AdjoinRoot (C.polynomial i)) :=
    (C.monic i).finite_adjoinRoot
  let E : V ≃ₗ[K] ((i : C.ι) → AdjoinRoot (C.polynomial i)) :=
    (Module.AEval'.of A).trans (C.equiv.restrictScalars K)
  have hE (v : V) : E (A v) =
      LinearMap.piMap (fun i : C.ι => rootOperator (C.polynomial i)) (E v) := by
    funext i
    have he := congrFun (C.equiv.map_smul (X : K[X]) (Module.AEval'.of A v)) i
    rw [Module.AEval.X_smul_of] at he
    have he' : E (A v) i = (X : K[X]) •
        (show K[X] ⧸ Submodule.span K[X] ({C.polynomial i} : Set K[X]) from E v i) := he
    exact he'.trans (quotient_X_smul (C.polynomial i) (E v i))
  have hc : E.conj A = LinearMap.piMap
      (fun i : C.ι => rootOperator (C.polynomial i)) := by
    apply LinearMap.ext
    intro x
    change E (A (E.symm x)) = _
    rw [hE,E.apply_symm_apply]
  calc
    _ = (E.conj A).charpoly := (E.charpoly_conj A).symm
    _ = (LinearMap.piMap (fun i : C.ι => rootOperator (C.polynomial i))).charpoly := by
      rw [hc]
    _ = ∏ i : C.ι, (rootOperator (C.polynomial i)).charpoly :=
      FiniteIndexedCharacteristicPolynomial.charpoly_pi K
        (fun i : C.ι => AdjoinRoot (C.polynomial i)) (fun i => rootOperator (C.polynomial i))
    _ = _ := Finset.prod_congr rfl (fun i _ => rootOperator_charpoly _ (C.monic i))

theorem code_prod {A : Module.End K V}
    (C : LinearMapPositiveCyclicDecomposition.Chart A) :
    (LinearMapCyclicCodeEquivalence.code C).prod = A.charpoly := by
  calc
    _ = ∏ i : C.ι, C.polynomial i := rfl
    _ = _ := (charpoly_eq_prod C).symm

end SymmetricSubgroupAsymptotics.LinearMapCyclicCodeCharacteristicPolynomial
