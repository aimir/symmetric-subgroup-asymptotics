import SymmetricSubgroupAsymptotics.CFSGSymplecticTernaryScalars
import SymmetricSubgroupAsymptotics.CFSGSymplecticFirstTorusShortExtraction

/-! Extract the original first short-root line and pure Coxeter word from
the literal ternary pair, uniformly in every symplectic rank at least two. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticTernaryExtraction
open CFSGSymplecticSerreMatrices CFSGSymplecticTernaryScalars

theorem pair_extract {K : Type} [Field K] [Finite K]
    (hcard : Nat.card K = 3) (r : ℕ) (hr : 0 < r)
    (H : Subgroup (elementaryRootGroup K (r + 1)))
    (hx : secondLongRoot K r 1 ∈ H) (hy : cleanMixedWeyl K r ∈ H) :
    coxeterWeyl K r ∈ H ∧
      (∀ a : K, initialShortRoot K r a ∈ H) ∧
      (∀ a : K, secondLongRoot K r a ∈ H) := by
  have hB : ∀ a : K, secondLongRoot K r a ∈ H :=
    root_line_mem hcard (secondLongRoot K r) (secondLongRoot_zero K r)
      (secondLongRoot_add K r) H hx
  have hupper := firstLongRoot_mem_of_cleanMixed K r hr H hy hB
  have hlower := firstLowerLongRoot_mem_of_cleanMixed K r hr H hy hupper
  have ht := firstTorus_mem_of_long_lines K r H hupper hlower (-1)
  have ha : initialShortRoot K r 1 ∈ H := by
    have he := initial_short_extraction_mem K r hr (-1) H ht hy
    rw [extraction_coefficient hcard] at he
    exact he
  have hA : ∀ a : K, initialShortRoot K r a ∈ H :=
    root_line_mem hcard (initialShortRoot K r) (initialShortRoot_zero K r)
      (initialShortRoot_add K r) H ha
  have hw : coxeterWeyl K r ∈ H := by
    have he := H.mul_mem (H.inv_mem ha) hy
    simpa only [cleanMixedWeyl, inv_mul_cancel_left] using he
  exact ⟨hw, hA, hB⟩

end SymmetricSubgroupAsymptotics.CFSGSymplecticTernaryExtraction
