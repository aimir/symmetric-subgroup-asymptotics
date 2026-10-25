import SymmetricSubgroupAsymptotics.QuaternaryPauliUnitaryRepresentation
import Mathlib.Tactic.Abel

/-! The SAME displayed Fourier/phase elements conjugate the ACTUAL
Pauli27 by explicit coordinate automorphisms. Quotient rotation/shear
and the central carry are retained. Dense Fourier products reduce to
ONE supported monomial entry, not a table of group elements. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.QuaternaryPauliFourierPhaseNormalization
open CFSGHeisenbergCoordinateGroup QuaternaryPauliHeisenbergRepresentation
open QuaternaryPauliUnitaryRepresentation

def phaseTerm (a : P) : P := 2*a*(a-1)

theorem phaseTerm_add : ∀ a b : P, phaseTerm (a+b)=phaseTerm a+phaseTerm b+a*b := by
  decide +kernel

def rotation : MulAut Heis where
  toFun g := ⟨-g.b,g.a,g.c-g.a 0*g.b 0⟩
  invFun g := ⟨g.b,-g.a,g.c-g.a 0*g.b 0⟩
  left_inv g := by
    apply Element.ext
    · rfl
    · funext i; change - -g.b i=g.b i; exact neg_neg _
    · change (g.c-g.a 0*g.b 0)-(-g.b 0)*g.a 0=g.c
      ring
  right_inv g := by
    apply Element.ext
    · funext i; change - -g.a i=g.a i; exact neg_neg _
    · rfl
    · change (g.c-g.a 0*g.b 0)-g.b 0*(-g.a 0)=g.c
      ring
  map_mul' g h := by
    apply Element.ext
    · funext i
      change -(g.b i+h.b i)= -g.b i+ -h.b i
      ring
    · rfl
    · change (g.c+h.c+dot g.b h.a)-(g.a 0+h.a 0)*(g.b 0+h.b 0)=
        (g.c-g.a 0*g.b 0)+(h.c-h.a 0*h.b 0)+dot g.a (-h.b)
      simp only [dot,Fin.sum_univ_one,Pi.neg_apply]
      ring

def shear : MulAut Heis where
  toFun g := ⟨g.a,g.b+g.a,g.c+phaseTerm (g.a 0)⟩
  invFun g := ⟨g.a,g.b-g.a,g.c-phaseTerm (g.a 0)⟩
  left_inv g := by
    apply Element.ext
    · rfl
    · funext i
      change (g.b i+g.a i)-g.a i=g.b i
      ring
    · change (g.c+phaseTerm (g.a 0))-phaseTerm (g.a 0)=g.c
      ring
  right_inv g := by
    apply Element.ext
    · rfl
    · funext i
      change (g.b i-g.a i)+g.a i=g.b i
      ring
    · change (g.c-phaseTerm (g.a 0))+phaseTerm (g.a 0)=g.c
      ring
  map_mul' g h := by
    apply Element.ext
    · rfl
    · funext i
      change (g.b i+h.b i)+(g.a i+h.a i)=(g.b i+g.a i)+(h.b i+h.a i)
      ring
    · change (g.c+h.c+dot g.b h.a)+phaseTerm (g.a 0+h.a 0)=
        (g.c+phaseTerm (g.a 0))+(h.c+phaseTerm (h.a 0))+dot (g.b+g.a) h.a
      rw [phaseTerm_add]
      simp only [dot,Fin.sum_univ_one,Pi.add_apply]
      ring

theorem rotation_coordinates (g : Heis) : ((rotation g).a 0,(rotation g).b 0)=(-g.b 0,g.a 0) := rfl

theorem shear_coordinates (g : Heis) : ((shear g).a 0,(shear g).b 0)=(g.a 0,g.b 0+g.a 0) := rfl

private theorem fourier_entry : ∀ i j : P,
    QuaternaryPauliUnitaryRepresentation.fourier.val.val i j=character (i*j) := by
  decide +kernel

private theorem phase_matrix : QuaternaryPauliUnitaryRepresentation.phase.val.val=
    Matrix.diagonal (fun i : P => character (phaseTerm i)) := by decide +kernel

private theorem fourier_left_entry (g : Heis) (i j : P) :
    (QuaternaryPauliUnitaryRepresentation.fourier.val.val*
      monomial (g.a 0) (g.b 0) g.c) i j=
      character (i*(j+g.a 0))*character (g.c+g.b 0*j) := by
  rw [Matrix.mul_apply,Finset.sum_eq_single (j+g.a 0)]
  · rw [fourier_entry]
    simp [monomial]
  · intro k _ hk
    rw [show monomial (g.a 0) (g.b 0) g.c k j=0 by simp [monomial,hk],mul_zero]
  · simp

private theorem fourier_right_entry (g : Heis) (i j : P) :
    (monomial (-g.b 0) (g.a 0) (g.c-g.a 0*g.b 0)*
      QuaternaryPauliUnitaryRepresentation.fourier.val.val) i j=
      character ((g.c-g.a 0*g.b 0)+g.a 0*(i+g.b 0))*character ((i+g.b 0)*j) := by
  rw [Matrix.mul_apply,Finset.sum_eq_single (i+g.b 0)]
  · rw [fourier_entry]
    have he : i=(i+g.b 0)+ -g.b 0 := by abel
    simp only [monomial,if_pos he]
  · intro k _ hk
    have he : i≠k+ -g.b 0 := by
      intro hi
      apply hk
      calc
        k=(k+ -g.b 0)+g.b 0 := by abel
        _ = i+g.b 0 := congrArg (fun a : P => a+g.b 0) hi.symm
    rw [show monomial (-g.b 0) (g.a 0) (g.c-g.a 0*g.b 0) i k=0 by
      simp [monomial,he],zero_mul]
  · simp

/-- The conjugating matrix and coordinate automorphism are both literal. -/
theorem fourier_normalizes (g : Heis) :
    QuaternaryPauliUnitaryRepresentation.fourier*
      QuaternaryPauliUnitaryRepresentation.representation g*
      QuaternaryPauliUnitaryRepresentation.fourier⁻¹=
      QuaternaryPauliUnitaryRepresentation.representation (rotation g) := by
  have he : QuaternaryPauliUnitaryRepresentation.fourier*
      QuaternaryPauliUnitaryRepresentation.representation g=
      QuaternaryPauliUnitaryRepresentation.representation (rotation g)*
        QuaternaryPauliUnitaryRepresentation.fourier := by
    apply Subtype.ext
    apply Units.ext
    funext i j
    change (QuaternaryPauliUnitaryRepresentation.fourier.val.val*
      monomial (g.a 0) (g.b 0) g.c) i j=
      (monomial (-g.b 0) (g.a 0) (g.c-g.a 0*g.b 0)*
        QuaternaryPauliUnitaryRepresentation.fourier.val.val) i j
    rw [fourier_left_entry,fourier_right_entry,←character_add,←character_add]
    congr 1
    ring
  rw [he,mul_inv_cancel_right]

/-- Phase conjugation retains its genuine central quadratic carry. -/
theorem phase_normalizes (g : Heis) :
    QuaternaryPauliUnitaryRepresentation.phase*
      QuaternaryPauliUnitaryRepresentation.representation g*
      QuaternaryPauliUnitaryRepresentation.phase⁻¹=
      QuaternaryPauliUnitaryRepresentation.representation (shear g) := by
  have he : QuaternaryPauliUnitaryRepresentation.phase*
      QuaternaryPauliUnitaryRepresentation.representation g=
      QuaternaryPauliUnitaryRepresentation.representation (shear g)*
        QuaternaryPauliUnitaryRepresentation.phase := by
    apply Subtype.ext
    apply Units.ext
    funext i j
    change (QuaternaryPauliUnitaryRepresentation.phase.val.val*
      monomial (g.a 0) (g.b 0) g.c) i j=
      (monomial (g.a 0) (g.b 0+g.a 0) (g.c+phaseTerm (g.a 0))*
        QuaternaryPauliUnitaryRepresentation.phase.val.val) i j
    simp only [phase_matrix,Matrix.diagonal_mul,Matrix.mul_diagonal]
    by_cases h : i=j+g.a 0
    · subst i
      simp only [monomial,if_true]
      rw [←character_add,←character_add,phaseTerm_add]
      congr 1
      ring
    · simp [monomial,h]
  rw [he,mul_inv_cancel_right]

end SymmetricSubgroupAsymptotics.QuaternaryPauliFourierPhaseNormalization
