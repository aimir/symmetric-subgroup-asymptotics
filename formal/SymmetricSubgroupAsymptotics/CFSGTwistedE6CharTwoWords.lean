import SymmetricSubgroupAsymptotics.CFSGTwistedE6A2CanonicalAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSingerSeven
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckA2Braid
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldOpposition
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalRootAdditive
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalTransport

/-! Literal matrix A2 words at the two fixed nodes of original twisted E6
in characteristic two. All relations are installed from the actual E6
integral Geck data; no source group relation is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedA2
open CFSGSerreQuadraticMatrix CFSGExceptionalGeckIntegralData
open CFSGExceptionalNormTwoBases CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
local instance twistedE6CharTwoWordsDecEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

abbrev CharTwoMatrixGroup (q : CFSG.PrimePower) :=
  (Matrix (E6Base.support⊕Roots CartanMatrix.E₆) (E6Base.support⊕Roots CartanMatrix.E₆) (q.Extension 2))ˣ

def charTwoRoots (q : CFSG.PrimePower) (neg : Bool) (i : Fin 2) : CharTwoMatrixGroup q :=
  (naturalRoot q neg i.rev 1).val

def charTwoOmega (q : CFSG.PrimePower) : CharTwoMatrixGroup q :=
  CFSGNormTwoGeckFieldOpposition.oppositionUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base (q.Extension 2)

private theorem reversed_pairing : CFSGIntegerMatrixPairing.integerPairing CartanMatrix.E₆
    (E6Index 3:Roots CartanMatrix.E₆).val (E6Index 1:Roots CartanMatrix.E₆).val= -1 := by
  rw [CFSGNormTwoGeckOrthogonalColumns.integerPairing_eq_cartan]
  have hh := congrFun (congrFun E6_cartan 1) 3
  change E6Base.cartanMatrix (E6Index 3) (E6Index 1)=CartanMatrix.E₆ 1 3 at hh
  exact hh.trans (by decide)

theorem charTwoRoots_square (q : CFSG.PrimePower) [CharP (q.Extension 2) 2]
    (neg : Bool) (i : Fin 2) : (charTwoRoots q neg i)^2=1 := by
  change (canonicalRoot E6Data (q.Extension 2) neg (node i.rev) 1)^2=1
  rw [pow_two,canonicalRoot_add,CharTwo.add_self_eq_zero]
  apply Units.ext
  simp only [canonicalRoot_val,zero_smul,zero_pow (by decide : (2:ℕ)≠0),add_zero,Units.val_one]

theorem charTwoRoots_braid (q : CFSG.PrimePower) [CharP (q.Extension 2) 2] :
    ((charTwoRoots q false 0*charTwoRoots q true 0*charTwoRoots q false 0)*
      (charTwoRoots q false 1*charTwoRoots q true 1*charTwoRoots q false 1))^3=1 := by
  have hraw := CFSGNormTwoGeckA2Braid.canonical_weyl_product_cube CartanMatrix.E₆
    CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index (q.Extension 2) 3 1 reversed_pairing
  have hh : (canonicalWeyl E6Data (q.Extension 2) 3*canonicalWeyl E6Data (q.Extension 2) 1)^3=1 := by
    simpa only [E6Data,canonicalWeyl_transportSource] using hraw
  change ((canonicalRoot E6Data (q.Extension 2) false 3 1*canonicalRoot E6Data (q.Extension 2) true 3 1*
    canonicalRoot E6Data (q.Extension 2) false 3 1)*(canonicalRoot E6Data (q.Extension 2) false 1 1*
      canonicalRoot E6Data (q.Extension 2) true 1 1*canonicalRoot E6Data (q.Extension 2) false 1 1))^3=1
  simpa only [canonicalWeyl,CharTwo.neg_eq] using hh

theorem charTwoRoots_singer (q : CFSG.PrimePower) [CharP (q.Extension 2) 2] :
    (charTwoRoots q false 0*(charTwoRoots q false 0*charTwoRoots q true 0*charTwoRoots q false 0)*
      (charTwoRoots q false 1*charTwoRoots q true 1*charTwoRoots q false 1))^7=1 := by
  have hraw := CFSGNormTwoGeckSingerSeven.canonical_singer_seven CartanMatrix.E₆
    CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index (q.Extension 2) 3 1 reversed_pairing
  have hh : (canonicalRoot E6Data (q.Extension 2) false 3 1*
      canonicalWeyl E6Data (q.Extension 2) 3*canonicalWeyl E6Data (q.Extension 2) 1)^7=1 := by
    simpa only [E6Data,canonicalRoot_transportSource,canonicalWeyl_transportSource] using hraw
  change (canonicalRoot E6Data (q.Extension 2) false 3 1*
    (canonicalRoot E6Data (q.Extension 2) false 3 1*canonicalRoot E6Data (q.Extension 2) true 3 1*
      canonicalRoot E6Data (q.Extension 2) false 3 1)*(canonicalRoot E6Data (q.Extension 2) false 1 1*
        canonicalRoot E6Data (q.Extension 2) true 1 1*canonicalRoot E6Data (q.Extension 2) false 1 1))^7=1
  simpa only [canonicalWeyl,CharTwo.neg_eq] using hh

theorem charTwoRoots_opposition (q : CFSG.PrimePower) (neg : Bool) (i : Fin 2) :
    charTwoOmega q*charTwoRoots q neg i*(charTwoOmega q)⁻¹=charTwoRoots q (!neg) i := by
  have hh := CFSGNormTwoGeckFieldOpposition.canonicalRoot_conjugate CartanMatrix.E₆
    CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index (q.Extension 2) neg (node i.rev) 1
  change charTwoOmega q*canonicalRoot E6Data (q.Extension 2) neg (node i.rev) 1*
    (charTwoOmega q)⁻¹=canonicalRoot E6Data (q.Extension 2) (!neg) (node i.rev) 1
  simpa only [charTwoOmega,E6Data,canonicalRoot_transportSource] using hh

end SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedA2
