import SymmetricSubgroupAsymptotics.CentralExtensionScalarPairingIndex

/-! In an actual scalar central extension over a two-element field,
a subgroup with zero quotient layer and missing the central one is
trivial. The central preimage is the same subgroup throughout. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryCentralExtensionZeroLayer
open CentralExtensionScalarPairingIndex
variable {F V N : Type*} [Field F] [AddCommGroup V] [Module F V] [Group N]

theorem central_range_not_le (D : Data (F := F) (V := V) (N := N))
    (J : Subgroup N) (hJ : D.central (Multiplicative.ofAdd (1 : F)) ∉ J) :
    ¬D.central.range ≤ J := by
  intro h
  exact hJ (h ⟨Multiplicative.ofAdd (1 : F),rfl⟩)

theorem eq_bot_of_projection_bot (hF : Nat.card F=2)
    (D : Data (F := F) (V := V) (N := N)) (J : Subgroup N)
    (hJ : D.central (Multiplicative.ofAdd (1 : F)) ∉ J)
    (hbot : J.map D.projection=⊥) : J=⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  have hp : D.projection x=1 := by
    have hm : D.projection x ∈ J.map D.projection := ⟨x,hx,rfl⟩
    rw [hbot] at hm
    exact Subgroup.mem_bot.mp hm
  have hk : x ∈ D.central.range := by
    rw [D.central_range]
    exact hp
  obtain ⟨z,hz⟩ := hk
  have hc : z.toAdd=0 ∨ z.toAdd=1 := by
    by_cases h : z.toAdd=0
    · exact Or.inl h
    obtain ⟨a,ha,hu⟩ := (Nat.card_eq_two_iff' (0 : F)).mp hF
    exact Or.inr ((hu z.toAdd h).trans (hu 1 one_ne_zero).symm)
  rcases hc with hzero | hone
  · have hz0 : z=1 := congrArg Multiplicative.ofAdd hzero
    exact Subgroup.mem_bot.mpr (hz.symm.trans
      ((congrArg D.central hz0).trans (map_one D.central)))
  · have hz1 : z=Multiplicative.ofAdd (1 : F) := congrArg Multiplicative.ofAdd hone
    exact False.elim (hJ (by rw [←hz1,hz]; exact hx))

end SymmetricSubgroupAsymptotics.BinaryCentralExtensionZeroLayer
