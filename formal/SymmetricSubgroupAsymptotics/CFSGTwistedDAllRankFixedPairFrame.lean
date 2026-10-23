import SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicTripleBridge
import SymmetricSubgroupAsymptotics.CFSGTwistedDNegativeSpaceCoordinates

/-! The checked literal relative hyperbolic-pair words give the exact
fixed-field frame in every natural rank at least two. The negative first
axis is kept explicit, including in the genuine rank-two base. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankFixedPairFrame
open CFSGOrthogonalDSerreMatrices CFSGTwistedDFixedQuadraticSpace
open CFSGTwistedDFixedQuadraticAction CFSGTwistedDSingularDimensionBound
open CFSGTwistedDRootPlaneImage CFSGTwistedDNegativeSpaceCoordinates
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedA2FixedField
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDGenerationForkTorus

private theorem zero_ne_last (n : ℕ) : (0 : Fin (n + 2)) ≠ last n := by
  intro he
  have hv := congrArg Fin.val he
  change 0 = n + 1 at hv
  omega

def negativeFirst (n : ℕ) (q : CFSG.PrimePower) : fixedSpace n q :=
  negativeBasis n q 0 (zero_ne_last n)

theorem negativeFirst_nonzero (n : ℕ) (q : CFSG.PrimePower) : negativeFirst n q ≠ 0 := by
  intro he
  have hv := congrArg (fun v : fixedSpace n q => v.val (Sum.inr 0)) he
  change (Pi.single (Sum.inr (0 : Fin (n + 2))) (1 : q.Extension 2) :
    Index (n + 2) → q.Extension 2) (Sum.inr 0) = 0 at hv
  rw [Pi.single_eq_same] at hv
  exact one_ne_zero hv

theorem negativeFirst_mem (n : ℕ) (q : CFSG.PrimePower) :
    negativeFirst n q ∈ negativeSpace n q := by
  rw [mem_negativeSpace_iff]
  intro i
  change (Pi.single (Sum.inr (0 : Fin (n + 2))) (1 : q.Extension 2) :
    Index (n + 2) → q.Extension 2) (Sum.inl i) = 0
  simp only [Pi.single_apply, Sum.inl_ne_inr, if_false]

theorem negativeFirst_succ (n : ℕ) (q : CFSG.PrimePower) :
    negativeFirst (n + 1) q = CFSGTwistedDHyperbolicTripleBridge.negativeAxis n q := rfl

theorem exists_fixed_pair_frame (n : ℕ) (q : CFSG.PrimePower)
    (v w : fixedSpace n q) (hv : v ≠ 0)
    (hvQ : fixedQuadraticForm n q v = 0) (hwQ : fixedQuadraticForm n q w = 0)
    (hB : (fixedQuadraticForm n q).polarBilin v w = 1) :
    ∃ g : relativeRootGroup n q,
      fixedLinearHom n q g v = firstAxis n q ∧
      fixedLinearHom n q g w = negativeFirst n q := by
  have hvK := congrArg (fun a : fixedField q => (a : q.Extension 2)) hvQ
  have hwK := congrArg (fun a : fixedField q => (a : q.Extension 2)) hwQ
  have hBK := congrArg (fun a : fixedField q => (a : q.Extension 2)) hB
  dsimp only at hvK hwK hBK
  rw [fixedQuadraticForm_apply] at hvK hwK
  rw [fixedQuadraticForm_polar,
    CFSGOrthogonalDIndexBundledQuadratic.splitQuadraticForm_polar] at hBK
  obtain ⟨g, hgv, hgw⟩ := CFSGTwistedDAllRankHyperbolicPairs.exists_normalize_pair
    n q v.val w.val v.property w.property hvK hwK
    (fun he => hv (Subtype.ext he)) hBK
  refine ⟨g, ?_, ?_⟩
  · apply Subtype.ext
    rw [fixedLinearHom_apply]
    exact hgv
  · apply Subtype.ext
    rw [fixedLinearHom_apply]
    exact hgw

end SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankFixedPairFrame
