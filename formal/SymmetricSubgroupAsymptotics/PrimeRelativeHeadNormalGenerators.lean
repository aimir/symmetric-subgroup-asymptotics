import SymmetricSubgroupAsymptotics.PrimeRelativeCharacterKernel

/-! Evaluation on an actual ambient normal-generating tuple bounds the
original relative character head. The mapped character kernel is normal
in the full original group, which is essential for this direction. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] {G : Type} [Group G]
    (N : Subgroup G) [N.Normal]

theorem primeRelativeHead_le_normal_generating_tuple {t : ℕ}
    (x : Fin t → G) (hx : Subgroup.normalClosure (Set.range x) = N) :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤ t := by
  let n : Fin t → N := fun i => ⟨x i, hx ▸
    Subgroup.subset_normalClosure (Set.mem_range_self i)⟩
  let ev : primeRelativeCharacters p N →ₗ[ZMod p] (Fin t → ZMod p) := {
    toFun := fun χ i => χ.1 (Additive.ofMul (n i))
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hev : Function.Injective ev := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro χ hχ
    have hz : ev χ = 0 := hχ
    have hN : N ≤ primeRelativeCharacterKernel p N χ := by
      calc
        N = Subgroup.normalClosure (Set.range x) := hx.symm
        _ ≤ primeRelativeCharacterKernel p N χ := by
          apply Subgroup.normalClosure_le_normal
          rintro _ ⟨i, rfl⟩
          exact (coe_mem_primeRelativeCharacterKernel_iff p N χ (n i)).mpr (congrFun hz i)
    apply Subtype.ext
    ext a
    exact (coe_mem_primeRelativeCharacterKernel_iff p N χ a).mp (hN a.2)
  have h := ev.finrank_le_finrank_of_injective hev
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, mul_one] using h

end SymmetricSubgroupAsymptotics

end
