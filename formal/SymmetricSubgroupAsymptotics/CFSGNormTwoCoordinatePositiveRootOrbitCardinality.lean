import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootCentralizerCardinality
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveCardinality
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateOrbitCardinality

/-! The actual positive-group conjugacy orbit of every lattice-labelled
root subgroup is small by the independently constructed commuting-root
normal words. The commuting-root count remains symbolic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootOrbitCardinality
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateRootHeightQuotient
open CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoCoordinateRootCentralizerCardinality CFSGNormTwoCoordinatePositiveCardinality
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

def positiveRootOrbit (K : Type) [Field K] (k : Roots A) :=
  Set.range (fun u : PositiveGroup A hd hs hp ho K=>
    (rootSubgroup A hd hs hp ho K k).map (MulAut.conj u.val).toMonoidHom)

theorem positive_root_orbit_card_mul_commuting_le (K : Type) [Field K] [Finite K]
    (k : Roots A) :
    Nat.card (positiveRootOrbit A hd hs hp ho K k)*
      Nat.card K^(commutingPositiveRoots A k).card≤Nat.card K^Nat.card (PositiveRoot A) := by
  calc
    _≤Nat.card (positiveRootOrbit A hd hs hp ho K k)*
        Nat.card (positiveRootCentralizer A hd hs hp ho K k) :=
      Nat.mul_le_mul_left _ (positive_root_centralizer_card_lower A hd hs hp ho K k)
    _≤Nat.card (PositiveGroup A hd hs hp ho K) :=
      CFSGSubgroupConjugateOrbitCardinality.conjugate_image_card_mul_centralizer_le
        (PositiveGroup A hd hs hp ho K) (rootSubgroup A hd hs hp ho K k)
    _=Nat.card K^Nat.card (PositiveRoot A) := positive_card A hd hs hp ho K

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootOrbitCardinality
