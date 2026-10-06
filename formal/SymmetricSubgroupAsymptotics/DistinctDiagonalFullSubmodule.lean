import SymmetricSubgroupAsymptotics.DiagonalInvariantSubmodules

/-!
# A full invariant submodule with distinct diagonal characters

If a diagonal scalar action has a different character on every coordinate,
then an invariant submodule which projects onto every coordinate is the whole
coordinate module.  This is the algebraic step needed in the four-sign
branch of the signed `F_3^4` module: no semisimplicity package and no
independently selected character list is used.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DiagonalInvariantSubmodules

open DiagonalIsotypeProjection

variable {k ι J : Type*} [Field k] [Fintype ι]

/-- Distinct literal scalar characters turn coordinatewise fullness into
the full module.  The proof projects an actual member of `K` onto the unique
isotype containing the requested coordinate. -/
theorem eq_top_of_fullCoordinates_of_injective
    (scalar : ι → J → k)
    (hscalar : Function.Injective scalar)
    (K : Stable scalar)
    (hfull : FullCoordinates K.1) :
    K.1 = ⊤ := by
  apply top_unique
  intro v _hv
  apply (mem_iff_isotypeProjection_mem scalar K.1 K.2 v).2
  intro a
  obtain ⟨i, hi⟩ := a.2
  obtain ⟨x, hx⟩ := hfull i (v i)
  have hprojection :
      isotypeProjection scalar a x.1 =
        isotypeProjection scalar a v := by
    funext j
    by_cases hj : scalar j = a.1
    · have hji : j = i := hscalar (hj.trans hi.symm)
      subst j
      simp only [isotypeProjection_apply, if_pos hi, hx]
    · simp only [isotypeProjection_apply, if_neg hj]
  rw [← hprojection]
  exact isotypeProjection_mem scalar K.1 K.2 a x.1 x.2

end DiagonalInvariantSubmodules
end SymmetricSubgroupAsymptotics

end
