import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckAdjacentPair
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckAdjacentCartanSign
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOffDiagonalCollecting
import Mathlib.Tactic.Group

/-! Reversing the adjacent simple labels reverses the root parameter in
the actual Weyl-conjugated root word. The A2 pair-word and square-sign
identities supply the equality integrally over every coefficient ring. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckAdjacentWeylExchange
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckAdjacentPair CFSGNormTwoGeckAdjacentCartanSign
open CFSGNormTwoGeckOffDiagonalCollecting
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

private theorem exchange_word {G : Type*} [Group G] (w v x y z : G)
    (hp : (w*v)*x*(w*v)⁻¹=z) (hsign : w^2*y=z*w^2) :
    w*y*w⁻¹=v*x*v⁻¹ := by
  calc
    _=w⁻¹*(w^2*y)*w⁻¹ := by group
    _=w⁻¹*(z*w^2)*w⁻¹ := by rw [hsign]
    _=w⁻¹*z*w := by group
    _=v*x*v⁻¹ := by rw [←hp];group

theorem adjacent_weyl_exchange (K : Type) [CommRing K] (i j : Fin r)
    (hij : cartan b s i j= -1) (hji : cartan b s j i= -1) (a : K) :
    canonicalWeyl (realizationData A hs hp b s) K i*
      canonicalRoot (realizationData A hs hp b s) K false j a*
      (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹=
    canonicalWeyl (realizationData A hs hp b s) K j*
      canonicalRoot (realizationData A hs hp b s) K false i (-a)*
      (canonicalWeyl (realizationData A hs hp b s) K j)⁻¹ := by
  let w := canonicalWeyl (realizationData A hs hp b s) K i
  let v := canonicalWeyl (realizationData A hs hp b s) K j
  let x := canonicalRoot (realizationData A hs hp b s) K false i (-a)
  let y := canonicalRoot (realizationData A hs hp b s) K false j a
  let z := canonicalRoot (realizationData A hs hp b s) K false j (-a)
  have hprod : (w*v)*x*(w*v)⁻¹=z :=
    adjacent_pair_word A hs hp b s K i j hij hji (-a)
  have hsign : w^2*y=z*w^2 :=
    adjacent_cartan_square_sign A hs hp b s i j hji K false a
  exact exchange_word w v x y z hprod hsign

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckAdjacentWeylExchange
