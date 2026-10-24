import SymmetricSubgroupAsymptotics.BinaryPlaneSingleKernelScalarAction
import SymmetricSubgroupAsymptotics.BinaryCubicScalarGeneratorTransfer
import SymmetricSubgroupAsymptotics.MonomialPolynomialOrbitGenerators
import Mathlib.Tactic.Convert

/-! Actual centralizer operators are monomial over the scalar field
constructed from the actual common cubic. A transitive actual centralizer
therefore supplies half-degree uniform generation for the larger group. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneSingleKernelScalarMonomial
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel
open BinaryPlaneOddKernelMultiplicityUniform (localKernel)
open BinaryPlaneSingleKernelScalarAction
open BinaryQuadraticField (Scalar omega)

variable {R I : Type} [Group R] [Finite R] [MulAction R I]
    [Fintype I] [DecidableEq I]
    (C : Subgroup (W (R := R) (I := I))) (i₀ : I)
    (hsingle : ∀ i : I, localKernel C i = localKernel C i₀)
    (hO : oddKernel C ≠ ⊥)

private theorem chart_single (i : I) (v : Plane) :
    functionChart C i₀ hsingle hO (Pi.single i v) =
      Pi.single i (coordinateChart C i₀ hsingle hO i v) := by
  funext j
  change coordinateChart C i₀ hsingle hO j ((Pi.single i v : I → Plane) j) =
    (Pi.single i (coordinateChart C i₀ hsingle hO i v) : I → Scalar) j
  by_cases hj : j = i
  · subst j
    rw [Pi.single_eq_same,Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hj,Pi.single_eq_of_ne hj,map_zero]

private theorem chart_symm_single (i : I) (a : Scalar) :
    (functionChart C i₀ hsingle hO).symm (Pi.single i a) =
      Pi.single i ((coordinateChart C i₀ hsingle hO i).symm a) := by
  apply (functionChart C i₀ hsingle hO).injective
  rw [LinearEquiv.apply_symm_apply,chart_single,LinearEquiv.apply_symm_apply]

omit [Finite R] [Fintype I] in
private theorem raw_single (h : C) (i : I) (v : Plane) :
    BinaryPlaneCyclicWreathUniform.representation C h (Pi.single i v) =
      Pi.single ((h : W (R := R) (I := I)).right • i)
        ((h : W (R := R) (I := I)).left ((h : W (R := R) (I := I)).right • i) v) := by
  let w : W (R := R) (I := I) := h.val
  funext j
  change w.left j ((Pi.single i v : I → Plane) (w.right⁻¹ • j)) =
    (Pi.single (w.right • i) (w.left (w.right • i) v) : I → Plane) j
  by_cases hj : j = w.right • i
  · subst j
    rw [inv_smul_smul,Pi.single_eq_same,Pi.single_eq_same]
  · have hn : w.right⁻¹ • j ≠ i := by
      intro h
      apply hj
      calc
        j = w.right • (w.right⁻¹ • j) := (smul_inv_smul _ _).symm
        _ = w.right • i := congrArg (fun z => w.right • z) h
    rw [Pi.single_eq_of_ne hn,Pi.single_eq_of_ne hj,map_zero]

/-- The scalar is an actual local coefficient, with no global character
or pure block lift assumed. -/
theorem scalar_monomial (h : centralizer C) (i : I) : ∃ a : Scalarˣ,
    scalarRepresentation C i₀ hsingle hO h (Pi.single i 1) =
      (a : Scalar) • (Pi.single
        ((((h : centralizer C) : C) : W (R := R) (I := I)).right • i) 1 : I → Scalar) := by
  let w : W (R := R) (I := I) := (h : C)
  let j := w.right • i
  let c : Scalar := coordinateChart C i₀ hsingle hO j
    (w.left j ((coordinateChart C i₀ hsingle hO i).symm 1))
  have hc : c ≠ 0 := by
    intro hz
    have h1 := (coordinateChart C i₀ hsingle hO j).injective
      (hz.trans (map_zero (coordinateChart C i₀ hsingle hO j)).symm)
    have h2 := (w.left j).injective (h1.trans (map_zero (w.left j)).symm)
    have h3 := congrArg (coordinateChart C i₀ hsingle hO i) h2
    have h10 : (1 : Scalar) = 0 := by
      simpa only [LinearEquiv.apply_symm_apply,map_zero] using h3
    exact one_ne_zero h10
  refine ⟨Units.mk0 c hc,?_⟩
  rw [scalarRepresentation_apply]
  change functionChart C i₀ hsingle hO
    (BinaryPlaneCyclicWreathUniform.representation C (h : C)
      ((functionChart C i₀ hsingle hO).symm (Pi.single i 1))) = _
  rw [chart_symm_single,raw_single,chart_single]
  change (Pi.single j c : I → Scalar) =
    (↑(Units.mk0 c hc) : Scalar) • (Pi.single j 1 : I → Scalar)
  rw [←Pi.single_smul]
  simp only [Units.val_mk0,smul_eq_mul,mul_one]

include hsingle hO in
/-- This theorem requires transitivity of the displayed ACTUAL
centralizer. The index-two, two-orbit case is not included by assumption. -/
theorem uniform_of_centralizer_transitive [Nontrivial I]
    (htrans : ∀ i j : I, ∃ h : centralizer C,
      ((((h : centralizer C) : C) : W (R := R) (I := I)).right • i) = j) :
    UniformSubrepresentationGeneratorBound (BinaryPlaneCyclicWreathUniform.representation C)
      (Nat.card I / 2) := by
  let H := centralizer C
  letI : MulAction H I := MulAction.compHom I
    ((PermutationalWreathProduct.rightHom : W (R := R) (I := I) →* R).comp
      (C.subtype.comp H.subtype))
  letI : MulAction.IsPretransitive H I := ⟨htrans⟩
  let rho2 := binaryRepresentation C i₀ hsingle hO
  let rho4 := scalarRepresentation C i₀ hsingle hO
  have hu4 : UniformSubrepresentationGeneratorBound rho4 (Nat.card I / 2) := by
    apply MonomialPolynomialOrbitGenerators.uniform_of_transitive rho4
    intro g x
    obtain ⟨u,hu⟩ := scalar_monomial C i₀ hsingle hO g x
    refine ⟨u,?_⟩
    convert hu using 1 <;> solve
      | rfl
      | dsimp only [rho4]
        congr 1
        funext j
        by_cases hj : j = x <;> simp [Pi.single,Function.update,hj]
      | funext j
        have hact : g • x = (((g : C) : W (R := R) (I := I)).right • x) := rfl
        rw [hact]
        by_cases hj : j = (((g : C) : W (R := R) (I := I)).right • x)
        · simp [Pi.single,Function.update,hj]
        · simp [Pi.single,Function.update,hj]
  have hu2 := BinaryCubicScalarGeneratorTransfer.uniform rho2 rho4
    (scalarRepresentation_apply C i₀ hsingle hO) (scalarGenerator C i₀ hsingle hO)
    (scalarGenerator_action C i₀ hsingle hO) hu4
  let rhoH := (BinaryPlaneCyclicWreathUniform.representation C).comp H.subtype
  let F := functionChart C i₀ hsingle hO
  let inter : Representation.IntertwiningMap rhoH rho2 := {
    toLinearMap := F.toLinearMap
    isIntertwining' h := by
      apply LinearMap.ext
      intro v
      change F (rhoH h v) = F (rhoH h (F.symm (F v)))
      rw [F.symm_apply_apply] }
  exact UniformSubrepresentationGeneratorBound.of_comp
    (BinaryPlaneCyclicWreathUniform.representation C) H.subtype (hu2.of_injective inter F.injective)

end SymmetricSubgroupAsymptotics.BinaryPlaneSingleKernelScalarMonomial
