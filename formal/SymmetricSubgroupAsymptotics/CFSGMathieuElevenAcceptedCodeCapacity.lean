import SymmetricSubgroupAsymptotics.CFSGMathieuElevenAcceptedCodes
import SymmetricSubgroupAsymptotics.CFSGMathieuElevenPrefixZeroExclusion
import SymmetricSubgroupAsymptotics.CFSGMathieuElevenPrefixOneCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuElevenPrefixTwoCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuElevenPrefixThreeCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuElevenPrefixFourCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuElevenPrefixFiveCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuElevenPrefixSixCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuElevenPrefixSevenCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuElevenPrefixEightCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuElevenPrefixNineCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuElevenPrefixTenCapacity

/-! The complete actual M11 accepted-image capacity is at most eight.
The already proved four-transversal cover and all eleven natural prefix
certificates supply completeness; only the eight whitelist elements are
retained. No outer/class/normalization assumption occurs in this module. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuElevenAcceptedCodeCapacity
open CFSG.Certificates.Mathieu11 CFSGMathieuElevenFourTransversalCover
open CFSGMathieuElevenFourTransversalSeedImages CFSGMathieuElevenAcceptedCodes

theorem accepts_decode_mem_acceptedCodes (c : Code) (h : Accepts (decode c)) :
    c∈acceptedCodes := by
  rcases c with ⟨⟨i,j⟩,⟨k,l⟩⟩
  fin_cases i
  · exact (CFSGMathieuElevenPrefixZeroExclusion.prefixZero_excluded j k l h).elim
  · exact CFSGMathieuElevenPrefixOneCapacity.prefix_complete j k l h
  · exact CFSGMathieuElevenPrefixTwoCapacity.prefix_complete j k l h
  · exact CFSGMathieuElevenPrefixThreeCapacity.prefix_complete j k l h
  · exact CFSGMathieuElevenPrefixFourCapacity.prefix_complete j k l h
  · exact CFSGMathieuElevenPrefixFiveCapacity.prefix_complete j k l h
  · exact CFSGMathieuElevenPrefixSixCapacity.prefix_complete j k l h
  · exact CFSGMathieuElevenPrefixSevenCapacity.prefix_complete j k l h
  · exact CFSGMathieuElevenPrefixEightCapacity.prefix_complete j k l h
  · exact CFSGMathieuElevenPrefixNineCapacity.prefix_complete j k l h
  · exact CFSGMathieuElevenPrefixTenCapacity.prefix_complete j k l h

def acceptedElements : Finset M11 := by
  classical
  exact acceptedCodes.image decode

theorem accepts_mem_acceptedElements (u : M11) (h : Accepts u) : u∈acceptedElements := by
  classical
  obtain ⟨c,rfl⟩ := decode_surjective u
  change decode c∈acceptedCodes.image decode
  exact Finset.mem_image.mpr ⟨c,accepts_decode_mem_acceptedCodes c h,rfl⟩

theorem acceptedElements_card_le_eight : acceptedElements.card≤8 := by
  classical
  change (acceptedCodes.image decode).card≤8
  exact Finset.card_image_le.trans acceptedCodes_card_le_eight

end SymmetricSubgroupAsymptotics.CFSGMathieuElevenAcceptedCodeCapacity
