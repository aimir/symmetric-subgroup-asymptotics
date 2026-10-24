import SymmetricSubgroupAsymptotics.GeneralThreeTwoTwentyOneSinger
import SymmetricSubgroupAsymptotics.IrreducibleAbelianSemidirectNormalGenerators

/-! A literal Singer matrix in an actual coordinate action forces
irreducibility on the original group, by pulling its actual invariant
subgroups through the specified group chart. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.BinaryTripleSingerIrreducible
open GeneralThreeTwoTwentyOneSinger

theorem irreducible_of_actual_singer
    {V H : Type} [CommGroup V] [Group H] (φ : H →* MulAut V)
    (b : V ≃* Multiplicative Vector)
    (f : H →* GeneralThreeTwoMatrixEncoding.Ambient)
    (hact : ∀ h v, (f h).val *ᵥ (b v).toAdd = (b (φ h v)).toAdd)
    (E : Subgroup H) (e : E) (hsinger : f e.val = singer) :
    IrreducibleAbelianSemidirect.Irreducible (φ.comp E.subtype) := by
  intro S hS
  let Q : AddSubgroup Vector := {
    carrier := {w | b.symm (Multiplicative.ofAdd w) ∈ S}
    zero_mem' := by
      change b.symm (Multiplicative.ofAdd (0 : Vector)) ∈ S
      rw [ofAdd_zero,map_one]
      exact S.one_mem
    add_mem' := by
      intro x y hx hy
      change b.symm (Multiplicative.ofAdd x * Multiplicative.ofAdd y) ∈ S
      rw [map_mul]
      exact S.mul_mem hx hy
    neg_mem' := by
      intro x hx
      change b.symm ((Multiplicative.ofAdd x)⁻¹) ∈ S
      rw [map_inv]
      exact S.inv_mem hx }
  have hQ : ∀ w ∈ Q, operator w ∈ Q := by
    intro w hw
    let v := b.symm (Multiplicative.ofAdd w)
    have hv : v ∈ S := hw
    have hh : φ e.val v ∈ S := hS e v hv
    have hb : (b v).toAdd = w := by
      dsimp only [v]
      rw [b.apply_symm_apply]
      rfl
    have he := hact e.val v
    rw [hsinger,hb] at he
    have hcoord : Multiplicative.ofAdd (operator w) = b (φ e.val v) :=
      Multiplicative.toAdd.injective he
    change b.symm (Multiplicative.ofAdd (operator w)) ∈ S
    rw [hcoord,b.symm_apply_apply]
    exact hh
  rcases invariantAddSubgroup_eq_bot_or_top Q hQ with hzero | hfull
  · left
    apply le_antisymm ?_ bot_le
    intro v hv
    have hmem : (b v).toAdd ∈ Q := by
      change b.symm (b v) ∈ S
      rw [b.symm_apply_apply]
      exact hv
    have hz : (b v).toAdd = 0 := AddSubgroup.mem_bot.mp (hzero ▸ hmem)
    have hb : b v = 1 := Multiplicative.toAdd.injective hz
    exact Subgroup.mem_bot.mpr (b.injective (hb.trans b.map_one.symm))
  · right
    apply top_le_iff.mp
    intro v _
    have hmem : (b v).toAdd ∈ Q := by rw [hfull]; exact AddSubgroup.mem_top _
    change b.symm (b v) ∈ S at hmem
    simpa only [b.symm_apply_apply] using hmem

end SymmetricSubgroupAsymptotics.BinaryTripleSingerIrreducible
