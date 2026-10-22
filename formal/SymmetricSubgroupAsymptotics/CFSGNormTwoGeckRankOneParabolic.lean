import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRankOneCells
import SymmetricSubgroupAsymptotics.CFSGRankOneBruhatSquareTorus
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelNormalization

/-! Exact rank-one parabolic installer. The remaining Weyl/torus
normalization premise is explicit here and must be proved for the actual
matrices before claiming an unconditional parabolic cover. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRankOneParabolic
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckBorelEnvelope
open CFSGNormTwoGeckBorelNormalization CFSGNormTwoGeckRankOneCells
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem parabolic_cover_of_weyl_torus (K : Type) [Field K] (i : Fin r)
    (hWT : ∀t∈torusGroup A hs hp b s K,
      canonicalWeyl (realizationData A hs hp b s) K i*t*
        (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹∈torusGroup A hs hp b s K) :
    ∀g∈Subgroup.closure ((borelEnvelope A hs hp b s K : Set _)∪
      {canonicalWeyl (realizationData A hs hp b s) K i}),
      CFSGRankOneBruhat.Cell (borelEnvelope A hs hp b s K)
        (rootGroup A hs hp b s K false)
        (canonicalWeyl (realizationData A hs hp b s) K i) g := by
  apply CFSGRankOneBruhatSquareTorus.closure_le_two_cells
    (borelEnvelope A hs hp b s K) (rootGroup A hs hp b s K false)
    (torusGroup A hs hp b s K) (canonicalWeyl (realizationData A hs hp b s) K i)
    le_sup_left le_sup_right le_rfl
    (le_trans le_sup_right (borelEnvelope_le_normalizer_positive A hs hp b s K)) hWT
  · simpa only [←pow_two] using weyl_square_mem_torus A hs hp b s K i
  · exact weyl_positive_cell A hs hp b s K i

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRankOneParabolic
