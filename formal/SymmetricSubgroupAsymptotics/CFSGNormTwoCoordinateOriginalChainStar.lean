import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootStarHom
import SymmetricSubgroupAsymptotics.CFSGExceptionalChainStarData
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalProjection

/-! The selected A-chain star survives in the ORIGINAL projective Serre
model. The positive matrix chart is proved injective by actual integral
root coefficients; the original projection is proved injective on that
literal positive group. No source-kernel assumption is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalChainStar
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateRootStarHom CFSGNormTwoCoordinateRootHeightQuotient
open CFSGNormTwoCoordinatePositiveQuotientInjectivity CFSGNormTwoCoordinateOriginalProjection
open CFSGGeckSerreRepresentation CFSGExceptionalChainStarData
variable {r n : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] (C : ChainStar A n)
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

def headFunctional : (Fin r→ℤ)→+ℤ where
  toFun v := v C.head
  map_zero' := rfl
  map_add' _ _ := rfl

def positiveStarHom : Multiplicative (Fin (n+1)→K)→*PositiveGroup A hd hs hp ho K :=
  positiveHom A hd hs hp ho K C.root C.pair

theorem positiveStarHom_injective : Function.Injective (positiveStarHom A hd hs hp ho K C) :=
  positiveHom_injective A hd hs hp ho K C.root C.pair (headFunctional A C) C.root_injective C.head_one

def originalStarHom [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    Multiplicative (Fin (n+1)→K)→*Projective (cartan b₀ s₀) K :=
  ((originalProjection A hd hs hp ho K i).comp (positiveInclusion A hd hs hp ho K)).comp
    (positiveStarHom A hd hs hp ho K C)

theorem originalStarHom_injective [Finite K] [Nontrivial (Fin r)]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    Function.Injective (originalStarHom A hd hs hp ho K C i) :=
  (originalProjection_positive_injective A hd hs hp ho K p i).comp
    (positiveStarHom_injective A hd hs hp ho K C)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalChainStar
