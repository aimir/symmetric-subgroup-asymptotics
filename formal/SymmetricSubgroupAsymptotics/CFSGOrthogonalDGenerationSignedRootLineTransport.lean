import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationRootLineTransport
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSignedRootConjugation

/-! All-parameter transport by the actual signed D Coxeter word. Its
nonzero sign ratio is absorbed by an explicit division of the requested
parameter; no root coefficient is replaced by an order or sign flag. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSignedRootLineTransport
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDBinaryCyclePermutation CFSGOrthogonalDGenerationCoxeterMonomial
open CFSGOrthogonalDGenerationSignedRootConjugation CFSGOrthogonalDGenerationRootLineTransport
variable (K : Type) [Field K]

private theorem coefficient_form (s : ℕ) (a b : Index (s + 2)) (t : K) :
    ((coxeterWeyl K (s + 1)).val : Mat K (s + 2)) * rootArray K a b t *
      (↑((coxeterWeyl K (s + 1)).val⁻¹) : Mat K (s + 2)) =
      rootArray K (cyclePerm s a) (cyclePerm s b)
        ((coxeterColumnSign K s a / coxeterColumnSign K s b) * t) := by
  rw [coxeter_conjugation, div_mul_eq_mul_div]

theorem coxeter_line_transfer (s : ℕ) (H : Subgroup (Mat K (s + 2))ˣ)
    (hW : (coxeterWeyl K (s + 1)).val ∈ H) (a b : Index (s + 2))
    (hA : HasRootLine H (rootArray K a b)) :
    HasRootLine H (rootArray K (cyclePerm s a) (cyclePerm s b)) :=
  conjugate_transfer H (coxeterWeyl K (s + 1)).val hW _ _ _
    (div_ne_zero (coxeterColumnSign_ne_zero K s a) (coxeterColumnSign_ne_zero K s b))
    (coefficient_form K s a b) hA

theorem inverse_coxeter_line_transfer (s : ℕ) (H : Subgroup (Mat K (s + 2))ˣ)
    (hW : (coxeterWeyl K (s + 1)).val ∈ H) (a b : Index (s + 2))
    (hA : HasRootLine H (rootArray K (cyclePerm s a) (cyclePerm s b))) :
    HasRootLine H (rootArray K a b) :=
  inverse_conjugate_transfer H (coxeterWeyl K (s + 1)).val hW _ _ _
    (coefficient_form K s a b) hA

theorem cleaned_coxeter_line_transfer (s : ℕ) (H : Subgroup (Mat K (s + 2))ˣ)
    (A : (Mat K (s + 2))ˣ) (hY : A * (coxeterWeyl K (s + 1)).val ∈ H)
    (a b : Index (s + 2))
    (hcomm : ∀ t, Commute (A : Mat K (s + 2))
      (rootArray K (cyclePerm s a) (cyclePerm s b) t))
    (hA : HasRootLine H (rootArray K a b)) :
    HasRootLine H (rootArray K (cyclePerm s a) (cyclePerm s b)) :=
  cleaned_word_transfer H A (coxeterWeyl K (s + 1)).val hY _ _ _
    (div_ne_zero (coxeterColumnSign_ne_zero K s a) (coxeterColumnSign_ne_zero K s b))
    (coefficient_form K s a b) hcomm hA

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSignedRootLineTransport
