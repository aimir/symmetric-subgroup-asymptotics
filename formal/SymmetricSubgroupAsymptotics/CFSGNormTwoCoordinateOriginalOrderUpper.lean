import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalFourFactorCover
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalFiniteWordMenu
import SymmetricSubgroupAsymptotics.FiniteFourFactorCoverCardinality

/-! An actual original-group order ceiling from the finite word menu and
the U-T-word-U cover. Every factor is counted on its literal image in the
same original projective group. No order formula or normalizer equality
is supplied as a premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOrderUpper
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoCoordinateOriginalRootFamily CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoCoordinateOriginalFourFactorCover CFSGNormTwoCoordinateOriginalFiniteWordMenu
variable {r:ℕ} (A:Matrix (Fin r) (Fin r) ℤ) (hd:∀i,A i i=2)
    (hs:A.transpose=A) (hp:(rationalMatrix A).PosDef) (ho:∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K:Type) [Field K] [Finite K] [Nontrivial (Fin r)]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem original_order_le
    (p:ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i:Fin r)
    (hneighbors:∀j,∃k,A j k= -1)
    (hn:¬IsMulCommutative (Projective (cartan b₀ s₀) K)) :
    Nat.card (Projective (cartan b₀ s₀) K)≤
      Nat.card K^Nat.card (PositiveRoot A)*Nat.card K^r*
        (2*Nat.card (Roots A))^r*Nat.card K^Nat.card (PositiveRoot A) := by
  letI : Finite (Projective (cartan b₀ s₀) K):=original_projective_finite A hd hs hp ho K i
  have hc:=FiniteFourFactorCoverCardinality.card_le_of_cover
    (positiveProjection A hd hs hp ho K i).range (torusProjection A hd hs hp ho K i).range
    (positiveProjection A hd hs hp ho K i).range
    (fun w:originalWordRange A hd hs hp ho K i=>w.val)
    (exists_original_four_factor A hd hs hp ho K i)
  exact hc.trans (Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.mul_le_mul (positiveProjection_card_le A hd hs hp ho K i)
      (torusProjection_card_le A hd hs hp ho K i))
      (originalWordRange_card_le A hd hs hp ho K p i hneighbors hn))
    (positiveProjection_card_le A hd hs hp ho K i))

theorem original_order_le_power
    (p:ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i:Fin r)
    (hneighbors:∀j,∃k,A j k= -1)
    (hn:¬IsMulCommutative (Projective (cartan b₀ s₀) K))
    (u c s:ℕ) (hpos:Nat.card (PositiveRoot A)≤u) (hroot:Nat.card (Roots A)≤c)
    (hmenu:2*c≤Nat.card K^s) :
    Nat.card (Projective (cartan b₀ s₀) K)≤Nat.card K^(2*u+r+s*r) := by
  have hq:1≤Nat.card K:=Nat.card_pos
  have hU:=Nat.pow_le_pow_right hq hpos
  have hW:=Nat.pow_le_pow_left ((Nat.mul_le_mul_left 2 hroot).trans hmenu) r
  apply (original_order_le A hd hs hp ho K p i hneighbors hn).trans
  calc
    Nat.card K^Nat.card (PositiveRoot A)*Nat.card K^r*(2*Nat.card (Roots A))^r*
        Nat.card K^Nat.card (PositiveRoot A)≤
      Nat.card K^u*Nat.card K^r*(Nat.card K^s)^r*Nat.card K^u :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_right _ hU) hW) hU
    _=Nat.card K^(2*u+r+s*r) := by ring

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOrderUpper
