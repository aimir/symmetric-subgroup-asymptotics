import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSimpleRootCells
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylSquareTorus
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticRootSubgroup

/-! The nonzero-parameter rank-one Gauss factor used in higher-rank
Bruhat multiplication: W_i U_i(a) belongs to B times a negative simple
root unit. It is proved from the actual parameterized Weyl/torus word. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSimpleGaussFactor
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckParameterizedWeyl CFSGNormTwoGeckParameterizedTorus
open CFSGNormTwoGeckWeylSquareTorus
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckSimpleRootCells
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem weyl_positive_nonzero_factor (K : Type) [Field K] (i : Fin r) (a : K) (ha : a≠0) :
    ∃c∈borelEnvelope A hs hp b s K,∃d : K,
      canonicalWeyl (realizationData A hs hp b s) K i*
        canonicalRoot (realizationData A hs hp b s) K false i a=
      c*canonicalRoot (realizationData A hs hp b s) K true i d := by
  let t : Kˣ := Units.mk0 (-a) (neg_ne_zero.mpr ha)
  let h := parameterTorus A hs hp b s K i t
  let u := canonicalRoot (realizationData A hs hp b s) K false i (t:K)
  have hh : h∈borelEnvelope A hs hp b s K :=
    (show torusGroup A hs hp b s K≤borelEnvelope A hs hp b s K from le_sup_right)
      (Subgroup.subset_closure ⟨(i,t),rfl⟩)
  have hu : u∈borelEnvelope A hs hp b s K := positive_mem_borel A hs hp b s K i (t:K)
  refine ⟨h⁻¹*u,(borelEnvelope A hs hp b s K).mul_mem
    ((borelEnvelope A hs hp b s K).inv_mem hh) hu,-(t:K)⁻¹,?_⟩
  have hw : canonicalWeyl (realizationData A hs hp b s) K i=
      h⁻¹*parameterWeyl A hs hp b s K i t := by
    dsimp only [h,parameterTorus]
    rw [parameterWeyl_one]
    group
  have hua : u*canonicalRoot (realizationData A hs hp b s) K false i a=1 := by
    dsimp only [u]
    rw [canonicalRoot_add]
    have ht : (t:K)+a=0 := by change -a+a=0;exact neg_add_cancel a
    rw [ht,canonicalRoot_zero]
  rw [hw]
  change (h⁻¹*(u*canonicalRoot (realizationData A hs hp b s) K true i (-(t:K)⁻¹)*u))*
    canonicalRoot (realizationData A hs hp b s) K false i a=_
  calc
    _=(h⁻¹*u)*canonicalRoot (realizationData A hs hp b s) K true i (-(t:K)⁻¹)*
        (u*canonicalRoot (realizationData A hs hp b s) K false i a) := by group
    _=_ := by rw [hua,mul_one]

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSimpleGaussFactor
