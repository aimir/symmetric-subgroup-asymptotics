import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRankOneParabolic
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylTorusNormalization

/-! The actual rank-one parabolic has its literal two-cell cover.
All torus and collecting inputs are supplied by the original matrices.
This is one simple-root parabolic, not a full higher-rank Bruhat cover. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRankOneParabolicProof
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckBorelEnvelope
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem parabolic_cover (K : Type) [Field K] (i : Fin r) :
    ∀g∈Subgroup.closure ((borelEnvelope A hs hp b s K : Set _)∪
      {canonicalWeyl (realizationData A hs hp b s) K i}),
      CFSGRankOneBruhat.Cell (borelEnvelope A hs hp b s K)
        (rootGroup A hs hp b s K false)
        (canonicalWeyl (realizationData A hs hp b s) K i) g :=
  CFSGNormTwoGeckRankOneParabolic.parabolic_cover_of_weyl_torus A hs hp b s K i
    (CFSGNormTwoGeckWeylTorusNormalization.weyl_conjugate_torus_mem A hs hp b s K i)

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRankOneParabolicProof
