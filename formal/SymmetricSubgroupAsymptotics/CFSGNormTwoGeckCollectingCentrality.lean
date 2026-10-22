import SymmetricSubgroupAsymptotics.CFSGAdditiveCollectingCentrality
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterizedCollecting
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalRootAdditive

/-! The actual simple root centralizes its adjacent positive Weyl
conjugate. This follows from the proved two-parameter collecting words
and literal root addition, with no extra Serre-group presentation input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckCollectingCentrality
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem adjacent_positive_fixed (K : Type*) [CommRing K] (i j : Fin r)
    (hij : cartan b s i j= -1) (t a : K) :
    canonicalRoot (realizationData A hs hp b s) K false i t*
      (canonicalWeyl (realizationData A hs hp b s) K i*
        canonicalRoot (realizationData A hs hp b s) K false j a*
        (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹)*
      (canonicalRoot (realizationData A hs hp b s) K false i t)⁻¹=
      canonicalWeyl (realizationData A hs hp b s) K i*
        canonicalRoot (realizationData A hs hp b s) K false j a*
        (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹ := by
  apply CFSGAdditiveCollectingCentrality.fixed_of_conjugation_factors
    (fun t=>canonicalRoot (realizationData A hs hp b s) K false i t)
    (fun a=>canonicalRoot (realizationData A hs hp b s) K false j a)
    (fun a=>canonicalWeyl (realizationData A hs hp b s) K i*
      canonicalRoot (realizationData A hs hp b s) K false j a*
      (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹)
  · intro t s
    exact (canonicalRoot_add _ K false i t s).symm
  · intro a b
    rw [←canonicalRoot_add]
    group
  · intro t a
    exact CFSGNormTwoGeckParameterizedCollecting.adjacent_conjugation_factor
      A hs hp b s K i j hij t a

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckCollectingCentrality
