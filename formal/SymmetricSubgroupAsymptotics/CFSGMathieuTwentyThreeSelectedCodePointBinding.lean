import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPointMaps
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeNormalizedFibreChart
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeActualRepresentation

/-! ONE selected code (1,2,3,6,4), no acceptance or capacity statement.
Only the frame/product caches and a cache of the reused five packed rows
are checked. Tail word transport supplies the actual chart shadow in a
separate semantic consumer. All points, including22, are retained. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeSelectedCodePointBinding
open CFSGMathieuTwentyTwoPackedPointMaps
open CFSGMathieuTwentyThreeNormalizedFibreChart
open CFSGMathieuTwentyThreePresentationWords

def frameForward (p : ℕ) : ℕ := packedGet 704382219158311228740691394971719 p
def frameInverse (p : ℕ) : ℕ := packedGet 12461642532497077337639091992855958 p

theorem frame_point_eq (p : Fin 23) :
    frameForward p.val = (conjugator.val p).val ∧
      frameInverse p.val = (conjugator.val.symm p).val := by
  fin_cases p <;> decide +kernel

def productForward (p : ℕ) : ℕ := packedGet 7832144073376446865039713993446986 p
def productInverse (p : ℕ) : ℕ := packedGet 5280439825730230421801465216062126 p

theorem product_point_eq (p : Fin 23) :
    productForward p.val = ((xPermutation*yPermutation) p).val ∧
      productInverse p.val = ((xPermutation*yPermutation).symm p).val := by
  fin_cases p <;> decide +kernel

def rawTailForward (p : ℕ) : ℕ :=
  if p < 22 then packedCandidateForward 1 2 3 6 4 p else p

def rawTailInverse (p : ℕ) : ℕ :=
  if p < 22 then packedCandidateInverse 1 2 3 6 4 p else p

def rawCandidateForward (p : ℕ) : ℕ :=
  frameForward (rawTailForward (frameInverse p))

def rawCandidateInverse (p : ℕ) : ℕ :=
  frameForward (rawTailInverse (frameInverse p))

def cachedCandidateForward (p : ℕ) : ℕ := packedGet 7318293465092673121784184227577344 p
def cachedCandidateInverse (p : ℕ) : ℕ := packedGet 23879055525865146745243304260640096 p

theorem candidate_cache_eq (p : Fin 23) :
    cachedCandidateForward p.val = rawCandidateForward p.val ∧
      cachedCandidateInverse p.val = rawCandidateInverse p.val := by
  fin_cases p <;> decide +kernel

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeSelectedCodePointBinding
