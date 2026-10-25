import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovAction
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightSelectedAction
import SymmetricSubgroupAsymptotics.CFSGFFourNormCertificateSparsePowers
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightPrimePeriod

/-! An unconditional109 proper-index bound for the literal original
ReeF4(8). The selected actual fixed word has a certified moving vector
of period109. Its central quotient kernel lies in the SAME proved Borel,
whose order is prime to109. No word-period hypothesis remains. -/
set_option autoImplicit false
set_option Elab.async false
-- The selected word has70 compositional roots; keep elaborator recursion local.
set_option maxRecDepth 4096
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightPrimeIndex
open CFSGReeFFourFieldEightCertificateField
open CFSGReeFFourFieldEightKrylovAction CFSGReeFFourFieldEightSelectedAction
open CFSGReeFFourFieldEightFixedSelectedWord CFSGReeFFourFieldEightKrylovData
open CFSGReeFFourFieldEightWordTemplates CFSGFFourNormCertificateSparseWords
open CFSGFFourNormCertificateSparsePowers CFSGReeFFourFieldParameters
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourPerfectProjection
open CFSGReeFFourFixedAmbientHom CFSGReeFFourFieldEightPrimePeriod
open CFSGReeFFourFixedBorelCardinality

private instance fixedFinite : Finite (originalModelFixed 1) :=
  Finite.of_injective (fixedAmbientHom 1) (fixedAmbientHom_injective 1)
private instance originalFinite : Finite (CFSG.Models.ReeF4 1) :=
  Finite.of_surjective (fixedToOriginal 1 (by omega))
    (fixedToOriginal_surjective 1 (by omega))

def selectedVector : Fin 26 → Field 1 := fun j => fieldEquiv (vectors 0 j)

private theorem word_period_transport (s : List Letter) (v : Fin 26 → Element)
    (hperiod : (wordEnd Element (RingHom.id Element) s ^ 109) v = v) :
    (wordEnd (Field 1) fieldEquiv.toRingHom s ^ 109) (fun j => fieldEquiv (v j)) =
      (fun j => fieldEquiv (v j)) := by
  have h := wordEnd_pow_map_apply (Field 1) fieldEquiv.toRingHom s 109 v
  rw [hperiod] at h
  exact h.symm

private theorem fixed_period_of_word (g : originalModelFixed 1)
    (s : List Letter) (v : Fin 26 → Element)
    (hg : fixedLinearAction g = wordEnd (Field 1) fieldEquiv.toRingHom s)
    (hperiod : (wordEnd Element (RingHom.id Element) s ^ 109) v = v) :
    fixedLinearAction (g ^ 109) (fun j => fieldEquiv (v j)) =
      (fun j => fieldEquiv (v j)) := by
  rw [map_pow, hg]
  exact word_period_transport s v hperiod

theorem selectedElement_period :
    fixedLinearAction (selectedElement ^ 109) selectedVector = selectedVector := by
  unfold selectedVector
  exact fixed_period_of_word selectedElement selectedLetters (vectors 0)
    selectedElement_action selected_period

theorem selectedElement_moved :
    fixedLinearAction selectedElement selectedVector ≠ selectedVector := by
  rw [selectedElement_action]
  intro h
  apply selected_moved
  funext j
  apply fieldEquiv.injective
  exact congrArg (fun w : Fin 26 → Field 1 => w j)
    ((wordEnd_map_apply (Field 1) fieldEquiv.toRingHom selectedLetters (vectors 0)).trans h)

theorem proper_index_le [IsSimpleGroup (CFSG.Models.ReeF4 1)]
    (H : Subgroup (CFSG.Models.ReeF4 1)) (hH : H ≠ ⊤) : 109 ≤ H.index := by
  letI : MulAction (originalModelFixed 1) (Fin 26 → Field 1) :=
    MulAction.ofEndHom fixedVectorAction
  apply PrimePeriodSimpleQuotientIndex.prime_le_proper_index_of_point_period
    109 (by decide +kernel) (fixedToOriginal 1 (by omega))
    (fixedToOriginal_surjective 1 (by omega)) (CFSGReeFFourFixedBorelCardinality.fixedBorel 1)
    quotient_kernel_le_borel ?_ selectedElement selectedVector ?_ ?_ H hH
  · rw [fixedBorel_card]
    norm_num
  · change fixedLinearAction (selectedElement ^ 109) selectedVector = selectedVector
    exact selectedElement_period
  · change fixedLinearAction selectedElement selectedVector ≠ selectedVector
    exact selectedElement_moved

end SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightPrimeIndex
