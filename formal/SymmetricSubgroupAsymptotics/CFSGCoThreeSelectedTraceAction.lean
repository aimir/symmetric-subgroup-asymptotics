import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedTraceTransitions
import SymmetricSubgroupAsymptotics.LinearMapSelectedKrylovPeriod

/-! All fourteen checked consecutive actions concern the SAME original
literal two-matrix word. They prove a return at14 and nonreturns at2,7 on
the selected e0 vector. No whole-matrix power identity is asserted. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedTraceAction
open CFSGCoThreeSelectedTraceData CFSGCoThreeSelectedTraceTransitions

def wordEnd : Module.End (ZMod 2) (Fin 22 → ZMod 2) :=
  (Matrix.mulVecLin a).comp (Matrix.mulVecLin b)

theorem consecutive (i : Fin 14) : wordEnd (vectors i.castSucc) = vectors i.succ := by
  change a *ᵥ (b *ᵥ vectors i.castSucc) = vectors i.succ
  rw [b_step,a_step]

theorem pow_initial (i : Fin 15) : (wordEnd^i.val) (vectors 0) = vectors i :=
  LinearMapSelectedKrylovPeriod.pow_apply_eq_vector wordEnd 14 vectors consecutive i

theorem return_fourteen : (wordEnd^14) (vectors 0) = vectors 0 := by
  have h : (wordEnd^14) (vectors 0) = vectors 14 := pow_initial ⟨14,by decide⟩
  exact h.trans final_eq_initial

theorem nonreturn_two : (wordEnd^2) (vectors 0) ≠ vectors 0 := by
  have h : (wordEnd^2) (vectors 0) = vectors 2 := pow_initial ⟨2,by decide⟩
  exact fun he => second_ne_initial (h.symm.trans he)

theorem nonreturn_seven : (wordEnd^7) (vectors 0) ≠ vectors 0 := by
  have h : (wordEnd^7) (vectors 0) = vectors 7 := pow_initial ⟨7,by decide⟩
  exact fun he => seventh_ne_initial (h.symm.trans he)

end SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedTraceAction
