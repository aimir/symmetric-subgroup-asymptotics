import SymmetricSubgroupAsymptotics.BinaryS16DirectPhysicalTarget

/-! # Numeric cast accessors for the direct S16 target -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16TargetCastAccessor

open SymmetricSubgroupAsymptotics
open BinaryS16DirectPhysicalTarget

/-- The two opposite half-degree casts used by the word chart cancel. -/
theorem finCast_symm_trans_cast
    {N N' : ℕ} (h : N = N') :
    (Equiv.cast (congrArg (fun M : ℕ ↦ Fin (2 * M)) h.symm)).trans
        (Equiv.cast (congrArg (fun M : ℕ ↦ Fin (2 * M)) h)) =
      Equiv.refl (Fin (2 * N')) := by
  subst N'
  rfl

end SymmetricSubgroupAsymptotics.BinaryS16TargetCastAccessor

end
