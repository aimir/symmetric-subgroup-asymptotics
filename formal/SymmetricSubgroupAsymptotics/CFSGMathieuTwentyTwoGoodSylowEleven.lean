import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoElevenGeneration
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoElevenNormalizerSolvable
import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrime

/-! The actual pinned M22 has a good Sylow prime11: literal recovery
words supply two generating Sylow conjugates and the actual normalizer
proof supplies solvability. No model identification or new callback is
assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoGoodSylowEleven

theorem goodSylowPrime : CFSGReduction.GoodSylowPrime CFSG.Models.Mathieu22 11 := by
  obtain ⟨P,g,hg⟩ := CFSGMathieuTwentyTwoElevenGeneration.two_conjugate_sylows
  exact ⟨by decide,P,g,CFSGMathieuTwentyTwoElevenNormalizerSolvable.normalizer_isSolvable P,hg⟩

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoGoodSylowEleven
