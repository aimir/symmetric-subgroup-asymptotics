import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRootOrthogonality
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryProjectiveRootLabels
import SymmetricSubgroupAsymptotics.CFSGSubgroupPairCommutation

/-! Intrinsic commutation of whole central-root subgroups is exactly
signed-Hermitian orthogonality of their actual natural centre labels. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUpperUnipotent CFSGSubgroupPairCommutation
open CFSGTwistedAUnitaryNaturalRadical

theorem conjugate_projective_rootLines_allCommute_iff (q : CFSG.PrimePower) (s : ℕ)
    (g h : naturalFixed (s + 3) q) :
    AllCommute (conjugateProjectiveCentralRootLine q s (unitaryProjectiveCover q s g))
        (conjugateProjectiveCentralRootLine q s (unitaryProjectiveCover q s h)) ↔
      unitaryNaturalPair q (s + 3) (unitaryCentralVector q s g) (unitaryCentralVector q s h) = 0 := by
  constructor
  · intro hcomm
    obtain ⟨b, hb0, hb⟩ := exists_nonzero_central_parameter q (s + 1)
    have hroot : centralFixed q (s + 1) b hb ∈ naturalCentralRootLine q (s + 1) :=
      (mem_naturalCentralRootLine_iff q (s + 1) _).mpr ⟨b, hb, rfl⟩
    have hmem (k : naturalFixed (s + 3) q) :
        unitaryProjectiveCover q s (k * centralFixed q (s + 1) b hb * k⁻¹) ∈
          conjugateProjectiveCentralRootLine q s (unitaryProjectiveCover q s k) := by
      rw [conjugateProjectiveCentralRootLine_cover]
      exact ⟨_, ⟨_, hroot, rfl⟩, rfl⟩
    exact (projective_central_roots_commute_iff_pair_zero q s g h b b hb hb hb0 hb0).mp
      (hcomm _ (hmem g) _ (hmem h))
  · intro hpair
    rw [conjugateProjectiveCentralRootLine_cover, conjugateProjectiveCentralRootLine_cover]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    obtain ⟨b, hb, rfl⟩ := (mem_naturalCentralRootLine_iff q (s + 1) u).mp hu
    obtain ⟨c, hc, rfl⟩ := (mem_naturalCentralRootLine_iff q (s + 1) v).mp hv
    by_cases hb0 : b = 0
    · subst b
      simp only [centralFixed_zero q (s + 1) hb, MulAut.conj_apply,
        mul_one, mul_inv_cancel, map_one, Commute.one_left]
    · by_cases hc0 : c = 0
      · subst c
        simp only [centralFixed_zero q (s + 1) hc, MulAut.conj_apply,
          mul_one, mul_inv_cancel, map_one, Commute.one_right]
      · exact (projective_central_roots_commute_iff_pair_zero q s g h b c hb hc hb0 hc0).mpr hpair

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
