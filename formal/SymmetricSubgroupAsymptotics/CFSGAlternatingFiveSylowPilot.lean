import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Data.Fin.VecNotation

/-! Selected sparse Fin5 identities for the actual A5 Sylow witness.
Only four displayed permutations and their sixteen pair products occur;
no collection of subgroups or elements of the full alternating group is
enumerated. The generic Sylow/normalizer argument is a separate consumer. -/
set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingFiveSylowPilot

abbrev A5 := alternatingGroup (Fin 5)

def double01 : A5 :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
    apply Equiv.Perm.mem_alternatingGroup.mpr
    decide +kernel⟩

def double02 : A5 :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by
    apply Equiv.Perm.mem_alternatingGroup.mpr
    decide +kernel⟩

def double03 : A5 :=
  ⟨Equiv.swap 0 3 * Equiv.swap 1 2, by
    apply Equiv.Perm.mem_alternatingGroup.mpr
    decide +kernel⟩

def element (i : Fin 4) : A5 := ![1, double01, double02, double03] i

def conjugator : A5 :=
  ⟨Equiv.swap 3 4 * Equiv.swap 2 3, by
    apply Equiv.Perm.mem_alternatingGroup.mpr
    decide +kernel⟩

theorem element_zero : element 0 = 1 := rfl

theorem element_injective : Function.Injective element := by decide +kernel

theorem element_mul_closed : ∀ i j : Fin 4,
    ∃ k : Fin 4, element i * element j = element k := by decide +kernel

theorem element_inv : ∀ i : Fin 4, (element i)⁻¹ = element i := by decide +kernel

theorem element_fix_four : ∀ i : Fin 4,
    (element i : Equiv.Perm (Fin 5)) (4 : Fin 5) = 4 := by decide +kernel

theorem common_fixed_iff : ∀ x : Fin 5,
    (∀ i : Fin 4, (element i : Equiv.Perm (Fin 5)) x = x) ↔ x = 4 := by decide +kernel

theorem conjugator_four : (conjugator : Equiv.Perm (Fin 5)) (4 : Fin 5) = 3 :=
  by decide +kernel

theorem two_subgroup_products_injective : Function.Injective
    (fun z : Fin 4 × Fin 4 => element z.1 *
      (conjugator * element z.2 * conjugator⁻¹)) := by decide +kernel

end SymmetricSubgroupAsymptotics.CFSGAlternatingFiveSylowPilot
