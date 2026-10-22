import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalLeadingHom
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateAdjacentLeadingNoncommute

/-! The adjacent-axis commutation obstruction on the SAME original
positive subgroup, transported by the proved actual positive-group
isomorphism. No ambient automorphism is lifted to the matrix model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalLeadingNoncommute
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

open CFSGNormTwoCoordinateOriginalLeadingHom CFSGNormTwoCoordinateAdjacentLeadingNoncommute
open CFSGNormTwoCoordinateLeadingFactor

theorem original_adjacent_leading_not_commute (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j k : Fin r)
    (u v : originalPositive A hd hs hp ho K i) (a b : K)
    (hjk : A j k= -1) (ha : a≠0) (hb : b≠0)
    (hu : originalLeadingHom A hd hs hp ho K p i u=
      Multiplicative.ofAdd (Pi.single j a : Fin r→K))
    (hv : originalLeadingHom A hd hs hp ho K p i v=
      Multiplicative.ofAdd (Pi.single k b : Fin r→K)) : ¬Commute u v := by
  intro hc
  let e := originalPositiveEquiv A hd hs hp ho K p i
  have hum := congrArg Multiplicative.toAdd hu
  have hvm := congrArg Multiplicative.toAdd hv
  change leadingCoordinates A hd hs hp ho K (e.symm u).val=(Pi.single j a : Fin r→K) at hum
  change leadingCoordinates A hd hs hp ho K (e.symm v).val=(Pi.single k b : Fin r→K) at hvm
  exact adjacent_leading_not_commute A hd hs hp ho K (e.symm u) (e.symm v)
    j k a b hjk ha hb hum hvm (hc.map e.symm.toMonoidHom)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalLeadingNoncommute
