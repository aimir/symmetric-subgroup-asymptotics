import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootString
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootSubgroup
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegativeWordCoefficients
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckGeneratedLieInvariance

/-! The actual root string for the original rootWitness coefficient.
Generated-Lie membership and degree are proved from the SAME actual
Weyl word and original negative operator, not supplied as new premises. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootWordString
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckNegativeWordCoefficients CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoGeckRationalWeylCollecting CFSGNormTwoGeckGeneratedLieInvariance
open CFSGGradedMatrixSupport
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
private abbrev CoordMat := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℚ
local notation "Mat" => CoordMat A hd hs hp ho
local notation "ell" => latticeWeight A hs hp b₀

def selectedCoefficient (k : Roots A) : Mat :=
  firstCoefficient A hs hp b₀ s₀ ℚ
    (rootWitness A hd hs hp ho k).val.1 (rootWitness A hd hs hp ho k).val.2

theorem selectedCoefficient_mem (k : Roots A) :
    selectedCoefficient A hd hs hp ho k∈RootPairing.GeckConstruction.lieAlgebra b₀ := by
  let p := rootWitness A hd hs hp ho k
  change firstCoefficient A hs hp b₀ s₀ ℚ p.val.1 p.val.2∈_
  rw [firstCoefficient,rational_F_eq]
  exact word_action_mem_generated A hs hp b₀ s₀ p.val.1 _
    (RootPairing.GeckConstruction.f_mem_lieAlgebra (s₀ p.val.2))

theorem selectedCoefficient_degree (k : Roots A) :
    Supported ell (fun v=>v+k.val) (selectedCoefficient A hd hs hp ho k) := by
  let p := rootWitness A hd hs hp ho k
  have hh := first_support A hs hp b₀ s₀ ℚ p.val.1 p.val.2
  rw [←p.property] at hh
  exact hh

theorem selected_lowering_after_raising (k : Roots A) (hk : ∀t,0≤k.val t) (i : Fin r)
    (hpair : integerPairing A k.val (s₀ i:Roots A).val= -1) :
    ⁅fieldRoot D ℚ true i,⁅fieldRoot D ℚ false i,selectedCoefficient A hd hs hp ho k⁆⁆=
      selectedCoefficient A hd hs hp ho k :=
  CFSGNormTwoCoordinateRootString.root_lowering_after_raising A hd hs hp ho k hk i hpair _
    (selectedCoefficient_mem A hd hs hp ho k) (selectedCoefficient_degree A hd hs hp ho k)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootWordString
