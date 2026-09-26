import SymmetricSubgroupAsymptotics.BinaryCarrierCommutatorWords16T1332
import SymmetricSubgroupAsymptotics.BinaryCarrierDerived16T1332
import SymmetricSubgroupAsymptotics.PrimeDerivedEvaluationPairing
import SymmetricSubgroupAsymptotics.PrimeAbelianizationGeneratorCoordinates
import SymmetricSubgroupAsymptotics.StarAlternatingSeparation
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FinCases

/-! The entire original 16T1332 commutator family is the four-parameter
star family. Original generation proves the five-coordinate map onto;
the full star family then proves it injective. No evaluation-space
dimension or independence of the original evaluations is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierStarTransport16T1332

abbrev Original := BinaryCarrierDerivedCharacters16T1332.Original
abbrev Characters := BinaryCarrierDerivedCharacters16T1332.Characters
abbrev U := Fin 4 → ZMod 2
abbrev Input := Fin 5 → ZMod 2
abbrev V := PrimeAbelianization 2 Original

private abbrev g := closureGenerators BinaryActionData16.node1332Generators
private abbrev kernelIdentity := BinaryCarrierDerived16T1332.evaluationKernel_eq_commutator

/-- The last original generator is the distinguished star coordinate. -/
def splitCoordinates : Input ≃ₗ[ZMod 2] U × ZMod 2 where
  toFun x := (fun i => x i.castSucc, x 4)
  invFun x := ![x.1 0, x.1 1, x.1 2, x.1 3, x.2]
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv x := by
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Complete character coordinates identify the original invariant
character space with the full dual of the horizontal star space. -/
def characterEquiv : Characters ≃ₗ[ZMod 2] Module.Dual (ZMod 2) U :=
  BinaryCarrierDerivedCharacters16T1332.coordinateEquiv.trans
    (Module.piEquiv (Fin 4) (ZMod 2) (ZMod 2))

theorem characterEquiv_apply (χ : Characters) (u : U) :
    characterEquiv χ u =
      ∑ i, u i * BinaryCarrierDerivedCharacters16T1332.coordinates χ i := by
  change Module.piEquiv (Fin 4) (ZMod 2) (ZMod 2)
    (BinaryCarrierDerivedCharacters16T1332.coordinates χ) u = _
  simpa only [smul_eq_mul] using
    Module.piEquiv_apply_apply (Fin 4) (ZMod 2) (ZMod 2)
      (BinaryCarrierDerivedCharacters16T1332.coordinates χ) u

/-- The exact map defined by the five literal original generators. -/
def generatorMap : Input →ₗ[ZMod 2] V := primeAbelianizationGeneratorMap 2 g

private theorem generatorMap_basis (i : Fin 5) :
    generatorMap (Pi.single i (1 : ZMod 2)) =
      primeAbelianizationMap 2 Original (Additive.ofMul (g i)) := by
  simp [generatorMap, primeAbelianizationGeneratorMap_apply, Pi.single_apply]

theorem generatorMap_surjective : Function.Surjective generatorMap :=
  primeAbelianizationGeneratorMap_surjective 2 g
    (closureGenerators_full BinaryActionData16.node1332Generators)

def form (χ : Characters) : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2 :=
  derivedEvaluationBilinear 2 kernelIdentity χ

/-- Equality of the actual pulled-back forms follows on the actual
five-generator basis, with every commutator already bound pointwise. -/
theorem pullback_form_eq (χ : Characters) :
    (form χ).compl₁₂ generatorMap generatorMap =
      (starAlternatingFamily (characterEquiv χ)).compl₁₂
        splitCoordinates.toLinearMap splitCoordinates.toLinearMap := by
  apply (Pi.basisFun (ZMod 2) (Fin 5)).ext
  intro i
  apply (Pi.basisFun (ZMod 2) (Fin 5)).ext
  intro j
  change form χ (generatorMap (Pi.basisFun (ZMod 2) (Fin 5) i))
      (generatorMap (Pi.basisFun (ZMod 2) (Fin 5) j)) =
    starAlternatingFamily (characterEquiv χ)
      (splitCoordinates (Pi.basisFun (ZMod 2) (Fin 5) i))
      (splitCoordinates (Pi.basisFun (ZMod 2) (Fin 5) j))
  rw [Pi.basisFun_apply, Pi.basisFun_apply]
  change derivedEvaluationBilinear 2 kernelIdentity χ
      (generatorMap (Pi.single i 1))
      (generatorMap (Pi.single j 1)) = _
  rw [generatorMap_basis, generatorMap_basis,
    derivedEvaluationBilinear_eval,
    BinaryCarrierCommutatorWords16T1332.original_commutator_value]
  fin_cases i <;> fin_cases j <;>
    simp [starAlternatingFamily_apply, characterEquiv_apply, splitCoordinates,
      BinaryCarrierCommutatorWords16T1332.values, Fin.sum_univ_succ, Pi.single_apply,
      CharTwo.sub_eq_add]

theorem pullback_form_apply (χ : Characters) (x y : Input) :
    derivedEvaluationBilinearMap 2 kernelIdentity χ (generatorMap x) (generatorMap y) =
      starAlternatingFamily (characterEquiv χ) (splitCoordinates x) (splitCoordinates y) :=
  congrArg (fun B : Input →ₗ[ZMod 2] Input →ₗ[ZMod 2] ZMod 2 => B x y)
    (pullback_form_eq χ)

/-- Full-family separation proves independence of the five original
evaluations, rather than requiring it as a coordinate assumption. -/
theorem generatorMap_injective : Function.Injective generatorMap :=
  linearMap_injective_of_pullback_star generatorMap splitCoordinates characterEquiv
    (derivedEvaluationBilinearMap 2 kernelIdentity) pullback_form_apply

def generatorEquiv : Input ≃ₗ[ZMod 2] V :=
  LinearEquiv.ofBijective generatorMap ⟨generatorMap_injective, generatorMap_surjective⟩

@[simp] theorem generatorEquiv_apply (x : Input) : generatorEquiv x = generatorMap x := rfl

/-- Star coordinates of the actual canonical evaluation space. -/
def evaluationEquiv : V ≃ₗ[ZMod 2] U × ZMod 2 :=
  generatorEquiv.symm.trans splitCoordinates

@[simp] theorem evaluationEquiv_generatorMap (x : Input) :
    evaluationEquiv (generatorMap x) = splitCoordinates x := by
  change splitCoordinates (generatorEquiv.symm (generatorEquiv x)) = splitCoordinates x
  rw [LinearEquiv.symm_apply_apply]

/-- The star identity for all actual characters and actual evaluation
vectors, with the original whole-group commutator pairing unchanged. -/
theorem actual_form_eq_star (χ : Characters) (x y : V) :
    derivedEvaluationBilinearMap 2
        BinaryCarrierDerived16T1332.evaluationKernel_eq_commutator χ x y =
      starAlternatingFamily (characterEquiv χ) (evaluationEquiv x) (evaluationEquiv y) := by
  obtain ⟨a, rfl⟩ := generatorMap_surjective x
  obtain ⟨b, rfl⟩ := generatorMap_surjective y
  rw [evaluationEquiv_generatorMap, evaluationEquiv_generatorMap]
  exact pullback_form_apply χ a b

end SymmetricSubgroupAsymptotics.BinaryCarrierStarTransport16T1332
