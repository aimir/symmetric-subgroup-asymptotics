import SymmetricSubgroupAsymptotics.CFSGSymplecticInitialTorusConjugates
import SymmetricSubgroupAsymptotics.CFSGTwoRootExtraction

/-! A pure long root extracted from two explicitly specified actual
C elements. This is the original elementary group, with no generation
hypothesis and no replacement by a classical-group model. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

def initialMixedWeyl (K : Type) [Field K] (r : ℕ) : elementaryRootGroup K (r + 1) :=
  initialShortRoot K r 1 * secondLongRoot K r 1 * coxeterWeyl K r

theorem initial_pure_long_extraction (K : Type) [Field K] (r : ℕ) (hr : 0 < r) (g : Kˣ) :
    ⁅initialMixedWeyl K r * initialTorus K r g * (initialMixedWeyl K r)⁻¹,
      initialTorus K r g⁆ = secondLongRoot K r ((1 - (g : K) ^ 2) ^ 2) := by
  exact CFSGTwoRootExtraction.two_root_double_commutator
    (initialShortRoot K r) (secondLongRoot K r)
    (initialShortRoot_add K r) (initialShortRoot_zero K r)
    (secondLongRoot_add K r) (secondLongRoot_zero K r)
    (initial_root_lines_commute K r hr)
    (initialTorus K r g) (coxeterWeyl K r) ((g : K) ^ 2)
    (if r = 1 then (g : K) ^ 2 else (g : K))
    (initialTorus_short_conjugation K r hr g)
    (initialTorus_long_conjugation K r hr g)
    (shiftedInitialTorus_short_conjugation K r hr g)
    (shiftedInitialTorus_long_conjugation K r hr g)
    (shiftedInitialTorus_commute K r hr g)

theorem initial_pure_long_mem (K : Type) [Field K] (r : ℕ) (hr : 0 < r) (g : Kˣ)
    (H : Subgroup (elementaryRootGroup K (r + 1)))
    (hx : initialTorus K r g ∈ H) (hy : initialMixedWeyl K r ∈ H) :
    secondLongRoot K r ((1 - (g : K) ^ 2) ^ 2) ∈ H := by
  rw [← initial_pure_long_extraction K r hr g, commutatorElement_def]
  have hz := H.mul_mem (H.mul_mem hy hx) (H.inv_mem hy)
  exact H.mul_mem (H.mul_mem (H.mul_mem hz hx) (H.inv_mem hz)) (H.inv_mem hx)

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
