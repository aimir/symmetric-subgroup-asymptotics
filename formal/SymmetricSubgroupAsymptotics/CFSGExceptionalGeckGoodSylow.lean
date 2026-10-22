import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateGoodSylow
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOriginalGoodSylow
import SymmetricSubgroupAsymptotics.CFSGExceptionalNormalizerWordIdentity
import SymmetricSubgroupAsymptotics.CFSGExceptionalGeckIntegralData

/-! Actual defining-prime good Sylow data for the ORIGINAL simple E6/E7/E8
Serre models. Every normalizer and generator is transported through the
actual source/image quotient; no named-group recognition input is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalGeckGoodSylow
open CFSG.Models.Chevalley CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
open CFSGExceptionalNormTwoBases CFSGExceptionalGeckIntegralData
open CFSGSignedCartanReflections CFSGExceptionalNormalizerWordIdentity
open CFSGNormTwoCoordinateGoodSylow CFSGNormTwoGeckOriginalGoodSylow
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local instance : DecidableEq (Roots CartanMatrix.E₇) := Classical.decEq _
local instance : DecidableEq (Roots CartanMatrix.E₈) := Classical.decEq _

theorem serreTypeE6_goodSylowPrime (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₆ K)] :
    CFSGReduction.GoodSylowPrime (Projective CartanMatrix.E₆ K) p := by
  have hgood := canonical_goodSylowPrime CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
    K E6Signs E6_signs_square E6_signs_cartan (E6_normalizer_word_identity K) p
  exact original_goodSylow_of_cartan_eq CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base E6Index E6_simple_sign K p E6_cartan hgood 0

theorem serreTypeE7_goodSylowPrime (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₇ K)] :
    CFSGReduction.GoodSylowPrime (Projective CartanMatrix.E₇ K) p := by
  have hgood := canonical_goodSylowPrime CartanMatrix.E₇ CartanMatrix.E₇_diag
    CartanMatrix.E₇_transpose E7_positive_definite CartanMatrix.E₇_off_diag_nonpos
    K E7Signs E7_signs_square E7_signs_cartan (E7_normalizer_word_identity K) p
  exact original_goodSylow_of_cartan_eq CartanMatrix.E₇ CartanMatrix.E₇_transpose
    E7_positive_definite E7Base E7Index E7_simple_sign K p E7_cartan hgood 0

theorem serreTypeE8_goodSylowPrime (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₈ K)] :
    CFSGReduction.GoodSylowPrime (Projective CartanMatrix.E₈ K) p := by
  have hgood := canonical_goodSylowPrime CartanMatrix.E₈ CartanMatrix.E₈_diag
    CartanMatrix.E₈_transpose E8_positive_definite CartanMatrix.E₈_off_diag_nonpos
    K E8Signs E8_signs_square E8_signs_cartan (E8_normalizer_word_identity K) p
  exact original_goodSylow_of_cartan_eq CartanMatrix.E₈ CartanMatrix.E₈_transpose
    E8_positive_definite E8Base E8Index E8_simple_sign K p E8_cartan hgood 0

theorem typeE6_goodSylowPrime (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.E6 q)] :
    CFSGReduction.GoodSylowPrime (CFSG.Models.E6 q) q.prime := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  exact serreTypeE6_goodSylowPrime q.Field q.prime

theorem typeE7_goodSylowPrime (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.E7 q)] :
    CFSGReduction.GoodSylowPrime (CFSG.Models.E7 q) q.prime := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  exact serreTypeE7_goodSylowPrime q.Field q.prime

theorem typeE8_goodSylowPrime (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.E8 q)] :
    CFSGReduction.GoodSylowPrime (CFSG.Models.E8 q) q.prime := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  exact serreTypeE8_goodSylowPrime q.Field q.prime

end SymmetricSubgroupAsymptotics.CFSGExceptionalGeckGoodSylow
