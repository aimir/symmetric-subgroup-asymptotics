import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationInitialElements
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCoxeterCoordinates

/-! Literal diagonal values needed by the odd B filter. The inverse
coordinate cycle is proved before the diagonal is unfolded, keeping the
penultimate, last and predecessor coordinates distinct in every rank. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationInitialDiagonalValues
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationInitialElements
open CFSGOrthogonalBGenerationForkTorus CFSGOrthogonalBGenerationCoxeterCoordinates
open CFSGOrthogonalBGenerationCoxeter
variable (K : Type) [Field K]

def beforeIndex (s : ℕ) : Fin (s + 3) := ⟨s, by omega⟩

def initialDiagonal (s : ℕ) (g : Kˣ) : Index (s + 3) → K := forkDiagonal K (s + 1) g
def shiftedDiagonal (s : ℕ) (g : Kˣ) : Index (s + 3) → K :=
  initialDiagonal K s g ∘ (coxeterCycle (s + 2)).symm

theorem initialDiagonal_values (s : ℕ) (g : Kˣ) :
    initialDiagonal K s g (pos (s + 3) (lastIndex s)) = (g : K) ∧
    initialDiagonal K s g (pos (s + 3) (penIndex s)) = (g : K) ∧
    initialDiagonal K s g (CFSGOrthogonalBSerreMatrices.neg (s + 3) (penIndex s)) = (g : K)⁻¹ ∧
    initialDiagonal K s g (CFSGOrthogonalBSerreMatrices.neg (s + 3) (lastIndex s)) = (g : K)⁻¹ ∧
    initialDiagonal K s g (middle (s + 3)) = 1 := by
  simp [initialDiagonal, forkDiagonal, CFSGOrthogonalDGenerationForkTorus.forkDiagonal,
    penIndex, lastIndex, CFSGOrthogonalDGenerationForkTorus.pen,
    CFSGOrthogonalDGenerationForkTorus.last, pos, CFSGOrthogonalBSerreMatrices.neg, middle]

theorem initialDiagonal_before (s : ℕ) (g : Kˣ) :
    initialDiagonal K s g (pos (s + 3) (beforeIndex s)) = 1 ∧
    initialDiagonal K s g (CFSGOrthogonalBSerreMatrices.neg (s + 3) (beforeIndex s)) = 1 := by
  have hp : beforeIndex s ≠ penIndex s := by
    intro he
    have hh := congrArg Fin.val he
    change s = s + 1 at hh
    omega
  have hl : beforeIndex s ≠ lastIndex s := by
    intro he
    have hh := congrArg Fin.val he
    change s = s + 2 at hh
    omega
  change initialDiagonal K s g (pos (s + 3) (beforeIndex s)) = 1 ∧ _
  simpa only [initialDiagonal, forkDiagonal, CFSGOrthogonalDGenerationForkTorus.forkDiagonal,
    Sum.elim_inl, pos, CFSGOrthogonalBSerreMatrices.neg,
    show CFSGOrthogonalDGenerationForkTorus.pen (s + 1) = penIndex s from rfl,
    show CFSGOrthogonalDGenerationForkTorus.last (s + 1) = lastIndex s from rfl,
    hp, hl, if_false] using (And.intro (rfl : (1 : K) = 1) (rfl : (1 : K) = 1))

theorem inverse_cycle_positive_last (s : ℕ) :
    (coxeterCycle (s + 2)).symm (pos (s + 3) (lastIndex s)) = pos (s + 3) (penIndex s) := by
  have hh : coxeterCycle (s + 2) (pos (s + 3) (penIndex s)) = pos (s + 3) (lastIndex s) := by
    simpa only [penIndex, lastIndex] using cycle_positive_shift (s + 2) (s + 1) (by omega)
  rw [← hh, Equiv.symm_apply_apply]

theorem inverse_cycle_negative_last (s : ℕ) :
    (coxeterCycle (s + 2)).symm (CFSGOrthogonalBSerreMatrices.neg (s + 3) (lastIndex s)) =
      CFSGOrthogonalBSerreMatrices.neg (s + 3) (penIndex s) := by
  have hh : coxeterCycle (s + 2) (CFSGOrthogonalBSerreMatrices.neg (s + 3) (penIndex s)) =
      CFSGOrthogonalBSerreMatrices.neg (s + 3) (lastIndex s) := by
    simpa only [penIndex, lastIndex] using cycle_negative_shift (s + 2) (s + 1) (by omega)
  rw [← hh, Equiv.symm_apply_apply]

theorem inverse_cycle_positive_pen (s : ℕ) :
    (coxeterCycle (s + 2)).symm (pos (s + 3) (penIndex s)) = pos (s + 3) (beforeIndex s) := by
  have hh : coxeterCycle (s + 2) (pos (s + 3) (beforeIndex s)) = pos (s + 3) (penIndex s) := by
    simpa only [penIndex, beforeIndex] using cycle_positive_shift (s + 2) s (by omega)
  rw [← hh, Equiv.symm_apply_apply]

theorem inverse_cycle_negative_pen (s : ℕ) :
    (coxeterCycle (s + 2)).symm (CFSGOrthogonalBSerreMatrices.neg (s + 3) (penIndex s)) =
      CFSGOrthogonalBSerreMatrices.neg (s + 3) (beforeIndex s) := by
  have hh : coxeterCycle (s + 2) (CFSGOrthogonalBSerreMatrices.neg (s + 3) (beforeIndex s)) =
      CFSGOrthogonalBSerreMatrices.neg (s + 3) (penIndex s) := by
    simpa only [penIndex, beforeIndex] using cycle_negative_shift (s + 2) s (by omega)
  rw [← hh, Equiv.symm_apply_apply]

theorem shiftedDiagonal_values (s : ℕ) (g : Kˣ) :
    shiftedDiagonal K s g (pos (s + 3) (lastIndex s)) = (g : K) ∧
    shiftedDiagonal K s g (pos (s + 3) (penIndex s)) = 1 ∧
    shiftedDiagonal K s g (CFSGOrthogonalBSerreMatrices.neg (s + 3) (penIndex s)) = 1 ∧
    shiftedDiagonal K s g (CFSGOrthogonalBSerreMatrices.neg (s + 3) (lastIndex s)) = (g : K)⁻¹ ∧
    shiftedDiagonal K s g (middle (s + 3)) = 1 := by
  have hm : (coxeterCycle (s + 2)).symm (middle (s + 3)) = middle (s + 3) := by
    apply (coxeterCycle (s + 2)).injective
    simp only [Equiv.apply_symm_apply, cycle_middle]
  simp only [shiftedDiagonal, Function.comp_apply, inverse_cycle_positive_last,
    inverse_cycle_positive_pen, inverse_cycle_negative_last, inverse_cycle_negative_pen, hm]
  exact ⟨(initialDiagonal_values K s g).2.1, (initialDiagonal_before K s g).1,
    (initialDiagonal_before K s g).2, (initialDiagonal_values K s g).2.2.1,
    (initialDiagonal_values K s g).2.2.2.2⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationInitialDiagonalValues
