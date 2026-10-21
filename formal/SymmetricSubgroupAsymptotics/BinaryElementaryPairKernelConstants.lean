import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport
import SymmetricSubgroupAsymptotics.BinaryPairFrameEquivariance
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

/-! In an original transitive elementary binary action, every physical
pair-kernel flip is constant and the full constant flip occurs. This binds
the regular16 elementary branch to the existing regular8 pair-layer chart. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin 8)) [MulAction.IsPretransitive U X]

/-- The actual kernel is the literal one-dimensional constant flip space.
The exponent condition is on the original faithful permutation source. -/
theorem kernelSpace_eq_constant_of_original_exponent_two
    (hpow : ∀ u : U, u ^ 2 = 1) :
    F.kernelSpace = Submodule.span (ZMod 2) {(1 : Fin 8 → ZMod 2)} := by
  have hcomm (u v : U) : u * v = v * u :=
    (Commute.of_orderOf_dvd_two
      (fun g => orderOf_dvd_iff_pow_eq_one.mpr (hpow g)) u v).eq
  letI : MulAction.IsPretransitive F.top.range (Fin 8) := F.top_pretransitive
  have hconstant (k : F.top.ker) (i j : Fin 8) : F.bits k i = F.bits k j := by
    obtain ⟨t, ht⟩ := MulAction.exists_smul_eq F.top.range i j
    obtain ⟨u, rfl⟩ := F.top.rangeRestrict_surjective t
    have he : MulAut.conjNormal u k = k := by
      apply Subtype.ext
      change u * (k : U) * u⁻¹ = (k : U)
      rw [hcomm]
      group
    have hb := F.bits_conjNormal u k j
    rw [he] at hb
    have hp : (F.top u)⁻¹ j = i := by
      change F.top u i = j at ht
      rw [← ht]
      exact (F.top u).symm_apply_apply i
    rw [hp] at hb
    exact hb.symm
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq U (F.frame (0, 0)) (F.frame (0, 1))
  have hfix : F.top u 0 = 0 := by
    have hh := F.intertwine u (0, 0)
    change (F.frame.symm (u • F.frame (0, 0))).1 = F.top u 0 at hh
    rw [hu, Equiv.symm_apply_apply] at hh
    exact hh.symm
  have htop : F.top u = 1 := by
    apply Equiv.ext
    intro i
    obtain ⟨t, ht⟩ := MulAction.exists_smul_eq F.top.range 0 i
    obtain ⟨v, rfl⟩ := F.top.rangeRestrict_surjective t
    change F.top v 0 = i at ht
    have hc : F.top u * F.top v = F.top v * F.top u := by
      rw [← map_mul, ← map_mul, hcomm]
    have hh := congrArg (fun p : Equiv.Perm (Fin 8) => p 0) hc
    change F.top u (F.top v 0) = F.top v (F.top u 0) at hh
    simpa only [ht, hfix] using hh
  let k : F.top.ker := ⟨u, htop⟩
  have hbit : F.bits k 0 = 1 := by
    have hh := F.kernel_action_frame k 0 0
    change u • F.frame (0, 0) = F.frame (0, 0 + F.bits k 0) at hh
    rw [hu, zero_add] at hh
    exact (congrArg Prod.snd (F.frame.injective hh)).symm
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    have hv : F.bits a.toMul = F.bits a.toMul 0 • (1 : Fin 8 → ZMod 2) := by
      funext i
      simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
      exact hconstant a.toMul i 0
    change F.bits a.toMul ∈ Submodule.span (ZMod 2) {(1 : Fin 8 → ZMod 2)}
    rw [hv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · apply Submodule.span_le.mpr
    rintro v hv
    rw [Set.mem_singleton_iff] at hv
    subst v
    refine ⟨Additive.ofMul k, ?_⟩
    funext i
    exact (hconstant k i 0).trans hbit

end SymmetricSubgroupAsymptotics.BinaryPairFrame
