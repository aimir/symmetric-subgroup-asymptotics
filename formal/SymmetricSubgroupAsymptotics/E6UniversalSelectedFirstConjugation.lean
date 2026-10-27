import SymmetricSubgroupAsymptotics.InvolutionBraidPresentation
import SymmetricSubgroupAsymptotics.CFSGYE6FirstConjugationBraidPilot

/-! Reuse the SAME checked literal Boolean trace in the universal E6
braid presentation, then map into ANY actual matching involution system.
The Y presentation's spider relation is never used in this proof. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.E6UniversalSelectedFirstConjugation
open InvolutionBraidTrace InvolutionBraidPresentation
open CFSGYE6SelectedWords (adjacent guideW)
open CFSGYE6FirstConjugationBraidPilot (start0 start1 trace0 certificate0 source_word)

 theorem universal_identity :
    value (InvolutionBraidPresentation.generator adjacent) start0=1 := by
  have hh := universal_word_identity_of_check adjacent start0 trace0 start1 certificate0
  simpa only [start1,value,List.map_nil,List.prod_nil] using hh

 theorem identity_in_system {G : Type*} [Group G] (S : System adjacent G) :
    value S.generator (guideW.reverse++[1]++guideW++[4])=1 := by
  have hh := congrArg (evaluation S) universal_identity
  rw [evaluation_value,map_one] at hh
  simpa only [source_word] using hh

end SymmetricSubgroupAsymptotics.E6UniversalSelectedFirstConjugation
