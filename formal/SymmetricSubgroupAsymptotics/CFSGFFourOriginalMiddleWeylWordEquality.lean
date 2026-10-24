import SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleWeylCertificateEquality
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn01
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn02
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn03
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn04
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn05
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn06
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn07
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn08
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn09
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn10
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn11
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn12
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn13
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn14
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn15
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn16
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn17
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn18
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn19
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn20
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn21
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn22
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn23
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn24
import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumn25

/-! All 26 independent kernel certificates, installed in the same faithful
norm26 action, give an unconditional equality of the two literal original
F4 words in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleWeylWordEquality
open CFSGFFourE6MiddleWeylColumnCertificate CFSGFFourOriginalMiddleWeylCertificateEquality
open CFSGFFourOriginalMiddleWeylColumnAction

private theorem allColumnCertificates_nonempty (k : Fin 26) : Nonempty (ColumnCertificate k) := by
  fin_cases k
  · exact ⟨zeroCertificate⟩
  · exact ⟨CFSGFFourE6MiddleWeylColumn01.certificate⟩
  · exact ⟨CFSGFFourE6MiddleWeylColumn02.certificate⟩
  · exact ⟨CFSGFFourE6MiddleWeylColumn03.certificate⟩
  · exact ⟨CFSGFFourE6MiddleWeylColumn04.certificate⟩
  · exact ⟨CFSGFFourE6MiddleWeylColumn05.certificate⟩
  · exact ⟨CFSGFFourE6MiddleWeylColumn06.certificate⟩
  · exact ⟨CFSGFFourE6MiddleWeylColumn07.certificate⟩
  · exact ⟨CFSGFFourE6MiddleWeylColumn08.certificate⟩
  · exact ⟨CFSGFFourE6MiddleWeylColumn09.certificate⟩
  · exact ⟨CFSGFFourE6MiddleWeylColumn10.certificate⟩
  · exact ⟨CFSGFFourE6MiddleWeylColumn11.certificate⟩
  · exact ⟨CFSGFFourE6MiddleWeylColumn12.certificate⟩
  · exact ⟨CFSGFFourE6MiddleWeylColumn13.certificate⟩
  · exact ⟨CFSGFFourE6MiddleWeylColumn14.certificate⟩
  · exact ⟨CFSGFFourE6MiddleWeylColumn15.certificate⟩
  · exact ⟨CFSGFFourE6MiddleWeylColumn16.certificate⟩
  · exact ⟨CFSGFFourE6MiddleWeylColumn17.certificate⟩
  · exact ⟨CFSGFFourE6MiddleWeylColumn18.certificate⟩
  · exact ⟨CFSGFFourE6MiddleWeylColumn19.certificate⟩
  · exact ⟨CFSGFFourE6MiddleWeylColumn20.certificate⟩
  · exact ⟨CFSGFFourE6MiddleWeylColumn21.certificate⟩
  · exact ⟨CFSGFFourE6MiddleWeylColumn22.certificate⟩
  · exact ⟨CFSGFFourE6MiddleWeylColumn23.certificate⟩
  · exact ⟨CFSGFFourE6MiddleWeylColumn24.certificate⟩
  · exact ⟨CFSGFFourE6MiddleWeylColumn25.certificate⟩

def allColumnCertificates (k : Fin 26) : ColumnCertificate k :=
  Classical.choice (allColumnCertificates_nonempty k)

theorem original_middle_word_equality (K : Type) [Field K] [Finite K] [CharP K 2] :
    originalLeftWord K=originalRightWord K :=
  original_words_eq_of_certificates K allColumnCertificates

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleWeylWordEquality
