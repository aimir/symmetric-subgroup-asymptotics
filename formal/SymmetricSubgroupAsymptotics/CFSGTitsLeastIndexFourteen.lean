import SymmetricSubgroupAsymptotics.PrimitiveSocleThirteenPointTitsExclusion
import SymmetricSubgroupAsymptotics.NonabelianSimpleProperIndex

/-! The proved actual Sylow divisor also bounds every proper subgroup
index when simplicity is inherited from the actual CFSG application.
The faithful coset action is constructed; no subgroup-index table is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsLeastIndexFourteen
open PrimitiveSocleRawStructure

theorem proper_index_fourteen_le [Finite CFSG.Models.Tits] [IsSimpleGroup CFSG.Models.Tits]
    (K : Subgroup CFSG.Models.Tits) (hK : K ≠ ⊤) : 14 ≤ K.index := by
  have hcore : K.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K.normalCore K.normalCore_normal with h | h
    · exact h
    · exact False.elim (hK (top_le_iff.mp (h ▸ K.normalCore_le)))
  let f : CFSG.Models.Tits →* Equiv.Perm (CFSG.Models.Tits ⧸ K) :=
    MulAction.toPermHom CFSG.Models.Tits (CFSG.Models.Tits ⧸ K)
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    exact (Subgroup.normalCore_eq_ker K).symm.trans hcore
  have h := PrimitiveSocleThirteenPointTitsExclusion.fourteen_le_card_of_injective f hf
  simpa only [← Subgroup.index_eq_card] using h

theorem least_index_fourteen_le [Finite CFSG.Models.Tits] [IsSimpleGroup CFSG.Models.Tits]
    (ell : ℕ) (hell : LeastProperIndex CFSG.Models.Tits ell) : 14 ≤ ell := by
  obtain ⟨K, hK, hindex⟩ := hell.1
  simpa only [hindex] using proper_index_fourteen_le K hK

end SymmetricSubgroupAsymptotics.CFSGTitsLeastIndexFourteen
