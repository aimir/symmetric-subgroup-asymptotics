import SymmetricSubgroupAsymptotics.BinaryPairStabilizerDescent
import SymmetricSubgroupAsymptotics.CoinducedPairIndexTwo

/-! The original point stabilizer has relative index two in its pair
stabilizer. For the nontrivial pair-kernel branch, a genuine kernel flip
supplies the two cosets and hence the actual coinduced pair filtration. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) [MulAction.IsPretransitive U X]

/-- The relative index is proved on the original stabilizers, using a
flip in the actual correlated kernel. -/
theorem pointStabilizer_relIndex_pairStabilizer
    (hker : F.top.ker ≠ ⊥) (i : I) :
    (F.pointStabilizer i).relIndex (F.pairStabilizer i) = 2 := by
  obtain ⟨k, hk⟩ := F.exists_kernel_bit_one hker i
  apply (F.pointStabilizer i).relIndex_eq_two_iff_exists_notMem_and'.mpr
  refine ⟨(k : U), ?_, ?_, ?_⟩
  · change F.top (k : U) i = i
    rw [MonoidHom.mem_ker.mp k.property]
    rfl
  · intro hfix
    have h : (k : U) • F.frame (i, 0) = F.frame (i, 0) := hfix
    change ((k : U) : Equiv.Perm X) (F.frame (i, 0)) = F.frame (i, 0) at h
    rw [F.kernel_action_frame, hk, zero_add] at h
    have hbit : (1 : ZMod 2) = 0 := congrArg Prod.snd (F.frame.injective h)
    exact one_ne_zero hbit
  · intro u hu
    have hui : F.top u i = i := hu
    have hbits : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide +kernel
    rcases hbits (F.offset u i) with hzero | hone
    · right
      change (u : Equiv.Perm X) (F.frame (i, 0)) = F.frame (i, 0)
      rw [F.action_frame, hui, hzero, add_zero]
    · left
      change ((k : U) : Equiv.Perm X)
        ((u : Equiv.Perm X) (F.frame (i, 0))) = F.frame (i, 0)
      rw [F.action_frame, hui, hone, zero_add, F.kernel_action_frame, hk]
      have htwo : (1 : ZMod 2) + 1 = 0 := by decide +kernel
      rw [htwo]

/-- The two-coset data for the actual point and pair stabilizers, ready
for the coinduced pair-sum construction. -/
def stabilizerTwoCosetData (hker : F.top.ker ≠ ⊥) (i : I) :
    CoinducedPairFiltration.TwoCosetData
      (F.pointStabilizer i) (F.pairStabilizer i)
      (F.pointStabilizer_le_pairStabilizer i) :=
  CoinducedPairFiltration.TwoCosetData.ofRelativeIndexTwo _ _ _
    (F.pointStabilizer_relIndex_pairStabilizer hker i)

end SymmetricSubgroupAsymptotics.BinaryPairFrame

end
