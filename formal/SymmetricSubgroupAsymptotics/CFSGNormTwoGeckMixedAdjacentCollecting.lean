import SymmetricSubgroupAsymptotics.CFSGA2MixedCommutator
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterizedCollecting
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckAdjacentCartanSign
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSelfRootConjugation

/-! Actual mixed-sign A2 collecting over the SAME integral Geck root
words. The third positive root is the literal Weyl conjugate, and the
output coefficient is one in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckMixedAdjacentCollecting
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckParameterizedCollecting CFSGNormTwoGeckAdjacentCartanSign
open CFSGNormTwoGeckSelfRootConjugation CFSGA2MixedCommutator
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem mixed_adjacent_word (K : Type) [CommRing K] (i j : Fin r)
    (hij : cartan b s i j= -1) (hji : cartan b s j i= -1) (a c : K) :
    ⁅canonicalRoot (realizationData A hs hp b s) K true i a,
      canonicalWeyl (realizationData A hs hp b s) K i*
        canonicalRoot (realizationData A hs hp b s) K false j c*
        (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹⁆=
      canonicalRoot (realizationData A hs hp b s) K false j (a*c) := by
  apply mixed_of_positive
    (fun t=>canonicalRoot (realizationData A hs hp b s) K false i t)
    (fun t=>canonicalRoot (realizationData A hs hp b s) K false j t)
    (fun t=>canonicalRoot (realizationData A hs hp b s) K true i t)
    (canonicalWeyl (realizationData A hs hp b s) K i)
  · intro t u
    simpa only [mul_comm u t] using adjacent_word A hs hp b s K i j hij t u
  · exact self_root_word A hs hp b s K i
  · exact adjacent_cartan_square_sign A hs hp b s i j hji K false

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckMixedAdjacentCollecting
