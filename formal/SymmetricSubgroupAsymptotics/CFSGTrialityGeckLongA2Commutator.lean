import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionRootLabels
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePairCollecting

/-! The three fixed long D4 roots form a literal A2 subsystem.  The
displayed word parameters have a primitive integer-unit commutator
constant, valid over every coefficient ring, including characteristics
two and three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckLongA2Commutator
open CFSGTrialityD4NormTwo CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckSectionRootLabels
open CFSGTrialityGeckFixedRootSections CFSGIntegerMatrixPairing
open CFSGNormTwoCoordinatePositivePairCollecting CFSGNormTwoCoordinateWordRootElementSign
open CFSGNormTwoCoordinateSimpleRootParametrization CFSGNormTwoCoordinateSelectedRootElement
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord

private abbrev selected (K : Type) [CommRing K]
    (k : CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) (t : K) :
    (Matrix GeckIndex GeckIndex K)ˣ :=
  selectedRootElement (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K k t

theorem longSection_selected_sign (s : Fin 3) :
    ∃ ε : ℤ,(ε = 1 ∨ ε = -1) ∧ ∀ (K : Type) [CommRing K] (t : K),
      longSection K s false t = selected K (longRoot s) ((ε : K)*t) := by
  obtain ⟨a,ha,hsimple⟩ := selected_simple_root_sign (CartanMatrix.D 4)
    (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4) D4_positive_definite
    (CartanMatrix.D_off_diag_nonpos 4) 1
  obtain ⟨b,hb,hword⟩ := word_selected_root_sign (CartanMatrix.D 4)
    (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4) D4_positive_definite
    (CartanMatrix.D_off_diag_nonpos 4) (longWord s) (Index 1)
  refine ⟨b*a,?_,?_⟩
  · rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> norm_num
  · intro K _ t
    have haa : (a : K)*((a : K)*t) = t := by
      rcases ha with rfl|rfl <;> simp
    have hbase : canonicalRoot rawData K false 1 t = selected K (Index 1) ((a : K)*t) := by
      have hh := hsimple K ((a : K)*t)
      change selected K (Index 1) ((a : K)*t) =
        canonicalRoot rawData K false 1 ((a : K)*((a : K)*t)) at hh
      rw [haa] at hh
      exact hh.symm
    have hw := hword K ((a : K)*t)
    change canonicalWord rawData K (longWord s) * selected K (Index 1) ((a : K)*t) *
        (canonicalWord rawData K (longWord s))⁻¹ =
      selected K (CFSGTrialityD4RelativeRootWords.rootWord (longWord s) (Index 1))
        ((b : K)*((a : K)*t)) at hw
    have hlabel : CFSGTrialityD4RelativeRootWords.rootWord (longWord s) (Index 1) = longRoot s := by
      rw [← long_seed_index]
      exact long_word_label s
    rw [hlabel] at hw
    calc
      longSection K s false t = canonicalWord rawData K (longWord s) *
          selected K (Index 1) ((a : K)*t) * (canonicalWord rawData K (longWord s))⁻¹ := by
        rw [longSection,longTransport_word,hbase]
      _ = selected K (longRoot s) ((b : K)*((a : K)*t)) := hw
      _ = selected K (longRoot s) (((b*a : ℤ) : K)*t) := by rw [Int.cast_mul,mul_assoc]

theorem long_pairing :
    integerPairing (CartanMatrix.D 4) (longRoot 0).val (longRoot 1).val = -1 := by decide

theorem long_sum :
    sumRoot (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      (longRoot 0) (longRoot 1) long_pairing = longRoot 2 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> decide

theorem long_commutator_sign :
    ∃ ε : ℤ,(ε = 1 ∨ ε = -1) ∧ ∀ (K : Type) [CommRing K] (a b : K),
      longSection K 0 false a * longSection K 1 false b *
        (longSection K 0 false a)⁻¹ * (longSection K 1 false b)⁻¹ =
      longSection K 2 false ((ε : K)*(a*b)) := by
  obtain ⟨u,hu,h0⟩ := longSection_selected_sign 0
  obtain ⟨v,hv,h1⟩ := longSection_selected_sign 1
  obtain ⟨w,hw,h2⟩ := longSection_selected_sign 2
  obtain ⟨c,hc,hcomm⟩ := positive_pair_commutator_sign (CartanMatrix.D 4)
    (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4) D4_positive_definite
    (CartanMatrix.D_off_diag_nonpos 4) (longRoot 0) (longRoot 1)
    (long_positive 0) (long_positive 1) long_pairing
  let ε : ℤ := w*c*u*v
  refine ⟨ε,?_,?_⟩
  · rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
      rcases hw with rfl|rfl <;> rcases hc with rfl|rfl <;> norm_num [ε]
  · intro K _ a b
    rw [h0 K a,h1 K b,h2 K ((ε : K)*(a*b))]
    have he := hcomm K ((u : K)*a) ((v : K)*b)
    rw [long_sum] at he
    change selected K (longRoot 0) ((u : K)*a) * selected K (longRoot 1) ((v : K)*b) *
        (selected K (longRoot 0) ((u : K)*a))⁻¹ *
        (selected K (longRoot 1) ((v : K)*b))⁻¹ =
      selected K (longRoot 2) ((w : K)*((ε : K)*(a*b)))
    trans selected K (longRoot 2) ((c : K)*(((u : K)*a)*((v : K)*b)))
    · exact he
    · apply congrArg (selected K (longRoot 2))
      have hww : (w : K)*(w : K) = 1 := by rcases hw with rfl|rfl <;> norm_num
      dsimp only [ε]
      simp only [Int.cast_mul]
      calc
        _ = ((w : K)*(w : K))*((c : K)*(((u : K)*a)*((v : K)*b))) := by rw [hww,one_mul]
        _ = _ := by ring

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckLongA2Commutator
