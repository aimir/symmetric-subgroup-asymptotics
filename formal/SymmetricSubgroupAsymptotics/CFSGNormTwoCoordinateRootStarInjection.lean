import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightLeading
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixOrderedFirstLayer

/-! Root-star parameters are separated by their genuine integral lattice
degrees, after any integral functional taking value one on the selected
roots. This includes the common head-coordinate of an A-chain star.
The argument applies in every characteristic and uses no logarithm or
assumed injectivity of a root product. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootStarInjection
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateRootBracketTransport CFSGNormTwoCoordinateRootCoefficientCoordinates
open CFSGNormTwoCoordinateRootHeightLeading CFSGNormTwoCoordinateSelectedRootElement
open CFSGGradedMatrixSupport CFSGGradedQuadraticUnit CFSGGradedMatrixSubgroups
open CFSGGradedMatrixLieFirstLayer CFSGGradedMatrixGroupFirstLayer
open CFSGGradedMatrixOrderedFirstLayer
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "ell" => latticeWeight A hs hp b₀
private abbrev CoordMat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K

def functionalWeight (H : (Fin r→ℤ)→+ℤ) : (b₀).support⊕Roots A→ℤ := H∘ell

theorem root_strict (K : Type) [Field K] (H : (Fin r→ℤ)→+ℤ)
    (k : Roots A) (hk : H k.val=1) (a : K) :
    selectedRootElement A hd hs hp ho K k a∈strictUnits (functionalWeight A hd hs hp ho H) := by
  apply strict_of_height_positive ell k.val H
  · refine ⟨a • selectedFieldCoefficient A hd hs hp ho K k,
      a^2 • selectedSecondCoefficient A hd hs hp ho K k,
      selectedRootElement_expansion A hd hs hp ho K k a,?_,?_⟩
    · exact supported_smul ell _ _ (selectedFieldCoefficient_support A hd hs hp ho K k) a
    · exact supported_smul ell _ _ (selectedSecondCoefficient_support A hd hs hp ho K k) (a^2)
  · omega

theorem root_firstLayer (K : Type) [Field K] (H : (Fin r→ℤ)→+ℤ)
    (k : Roots A) (hk : H k.val=1) (a : K) :
    firstLayer (functionalWeight A hd hs hp ho H) (selectedRootElement A hd hs hp ho K k a)=
      a • selectedFieldCoefficient A hd hs hp ho K k := by
  have hfirst : Supported (functionalWeight A hd hs hp ho H) (fun w=>w+1)
      (selectedFieldCoefficient A hd hs hp ho K k) := by
    simpa only [hk] using support_apply_height ell k.val H _
      (selectedFieldCoefficient_support A hd hs hp ho K k)
  have hsecond : Supported (functionalWeight A hd hs hp ho H) (fun w=>w+2)
      (selectedSecondCoefficient A hd hs hp ho K k) := by
    simpa only [map_add,hk] using support_apply_height ell (k.val+k.val) H _
      (selectedSecondCoefficient_support A hd hs hp ho K k)
  have hdev : (selectedRootElement A hd hs hp ho K k a : CoordMat A hd hs hp ho K)-1=
      a • selectedFieldCoefficient A hd hs hp ho K k+
        a^2 • selectedSecondCoefficient A hd hs hp ho K k := by
    rw [selectedRootElement_expansion]
    abel
  ext i j
  change (firstPart (functionalWeight A hd hs hp ho H) _ ) i j=_
  rw [hdev,firstPart_apply]
  by_cases hij : functionalWeight A hd hs hp ho H i=functionalWeight A hd hs hp ho H j+1
  · have hne : functionalWeight A hd hs hp ho H i≠functionalWeight A hd hs hp ho H j+2 := by omega
    rw [if_pos hij]
    simp only [Matrix.add_apply,Matrix.smul_apply,hsecond i j hne,smul_zero,add_zero]
  · rw [if_neg hij,Matrix.smul_apply,hfirst i j hij,smul_zero]

def rootProduct (K : Type) [Field K] {n : ℕ} (f : Fin n→Roots A) (v : Fin n→K) :
    (CoordMat A hd hs hp ho K)ˣ :=
  (List.ofFn (fun j=>selectedRootElement A hd hs hp ho K (f j) (v j))).prod

theorem rootProduct_firstLayer (K : Type) [Field K] (H : (Fin r→ℤ)→+ℤ)
    {n : ℕ} (f : Fin n→Roots A) (hf : ∀j,H (f j).val=1) (v : Fin n→K) :
    firstLayer (functionalWeight A hd hs hp ho H) (rootProduct A hd hs hp ho K f v)=
      ∑j,v j • selectedFieldCoefficient A hd hs hp ho K (f j) := by
  have hl : ∀u∈List.ofFn (fun j=>selectedRootElement A hd hs hp ho K (f j) (v j)),
      u∈strictUnits (functionalWeight A hd hs hp ho H) := by
    intro u hu
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hu
    exact root_strict A hd hs hp ho K H (f j) (hf j) (v j)
  have hh := (list_product_firstLayer (functionalWeight A hd hs hp ho H) _ hl).2
  have hterm (j : Fin n) := root_firstLayer A hd hs hp ho K H (f j) (hf j) (v j)
  simpa only [rootProduct,←List.ofFn_comp',List.sum_ofFn,hterm] using hh

theorem rootProduct_injective (K : Type) [Field K] (H : (Fin r→ℤ)→+ℤ)
    {n : ℕ} (f : Fin n→Roots A) (hf : Function.Injective f)
    (hH : ∀j,H (f j).val=1) : Function.Injective (rootProduct A hd hs hp ho K f) := by
  intro v w he
  have hh := congrArg (firstLayer (functionalWeight A hd hs hp ho H)) he
  rw [rootProduct_firstLayer A hd hs hp ho K H f hH,
    rootProduct_firstLayer A hd hs hp ho K H f hH] at hh
  exact root_family_coefficients_unique A hd hs hp ho K f hf v w hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootStarInjection
