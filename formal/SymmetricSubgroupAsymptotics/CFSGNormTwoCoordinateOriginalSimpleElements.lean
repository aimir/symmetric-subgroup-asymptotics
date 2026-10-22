import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalLeadingHom
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCommutingRoots
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalAdjointStrings

/-! Canonical simple-root elements in the literal ORIGINAL positive
subgroup have the exact single-coordinate parameters. Orthogonal such
elements commute by the actual Serre relation and integral transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSimpleElements
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoCoordinateOriginalPositiveCenter
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateLeadingHom
open CFSGNormTwoCoordinateDerivedFirstLayer CFSGNormTwoCoordinateRootLeadingAxes
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateOriginalAllRootLines
open CFSGNormTwoCoordinateOriginalProjection CFSGNormTwoCoordinatePositiveQuotientInjectivity
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Finite K] [Nontrivial (Fin r)]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

open CFSGNormTwoCoordinateOriginalLeadingHom CFSGNormTwoCoordinateLeadingHom

def originalSimpleElement (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r) (a : K) :
    originalPositive A hd hs hp ho K i :=
  (originalPositiveEquiv A hd hs hp ho K p i) (positiveRoot A hd hs hp ho K j a)

theorem originalSimpleElement_leading (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r) (a : K) :
    originalLeadingHom A hd hs hp ho K p i (originalSimpleElement A hd hs hp ho K p i j a)=
      Multiplicative.ofAdd (Pi.single j a : Fin r→K) := by
  rw [originalSimpleElement,originalLeadingHom_equiv_apply,leadingHom_positiveRoot]

theorem originalSimpleElement_commute (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j k : Fin r)
    (hjk : A j k=0) (a b : K) :
    Commute (originalSimpleElement A hd hs hp ho K p i j a)
      (originalSimpleElement A hd hs hp ho K p i k b) := by
  have hcartan : cartan b₀ s₀ j k=0 := by
    change (b₀).cartanMatrix (s₀ k) (s₀ j)=0
    rw [coordinate_cartan_transpose A hd hs hp ho]
    exact hjk
  have hm := CFSGSerreQuadraticCommutingRoots.roots_commute
    (CFSGNormTwoGeckIntegralRealization.realizationData A hs hp b₀ s₀) K j k
    (CFSGNormTwoGeckRationalAdjointStrings.lie_of_cartan_zero A hs hp b₀ s₀ j k hcartan) a b
  have hp' : Commute (positiveRoot A hd hs hp ho K j a) (positiveRoot A hd hs hp ho K k b) := by
    change _*_=_*_
    apply Subtype.ext
    exact hm.eq
  exact hp'.map (originalPositiveEquiv A hd hs hp ho K p i).toMonoidHom

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSimpleElements
