import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourTernarySylowLift

/-! Every physical block contains a moving orbit of the actual ternary
part of any original Sylow subgroup. The witness is obtained from the
proved onto local core coordinate and the original faithful block action;
no point, group, or module census is used. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (S : Sylow 3 (preE7NonPairAction w U))

/-- The fibre orbit and the ambient Sylow are the same ones used in the
subsequent block-times-fibre injection. -/
theorem degreeFourSylowCore_exists_fibre_orbit
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P ≠ ⊥)
    (i : block.Points) : ∃ x : Fin w, block.map x = i ∧
      3 ≤ Nat.card (MulAction.orbit (degreeFourSylowCore block P S) x) := by
  letI : Nontrivial (degreeFourLocalBinarySign block P).ker :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [degreeFourLocalBinarySign_ker_card block P hr]
      decide)
  obtain ⟨d, hd⟩ := exists_ne (1 : (degreeFourLocalBinarySign block P).ker)
  obtain ⟨a, ha⟩ := degreeFourSylowCoreCoordinate_surjective block P S hr hD i d
  let u : preE7NonPairAction w U := ((a.1 : S) : preE7NonPairAction w U)
  let C : block.Component := (ambientEmbedding block u).left i
  have hcoord : localMap block P C = (d : LocalQuotient block P) := by
    change (quotientEmbedding block P (QuotientGroup.mk' (E block P) u)).left i = _
    exact congrArg Subtype.val ha
  have hC : C ≠ 1 := by
    intro hc
    apply hd
    apply Subtype.ext
    rw [hc, map_one] at hcoord
    exact hcoord.symm
  have hmove : ∃ v : block.Fibre, C • v ≠ v := by
    by_contra hv
    push Not at hv
    apply hC
    apply Subtype.ext
    apply Equiv.ext
    intro v
    exact hv v
  obtain ⟨v, hv⟩ := hmove
  let e : block.Fibre × block.Points ≃ Fin w :=
    ActualBlockWreathEmbedding.productEquiv block.map block.map_equivariant block.base
  let x : Fin w := e (v, i)
  have hx : block.map x = i := by
    have he := congrArg Prod.snd (e.symm_apply_apply (v, i))
    exact he
  have htop : (ambientEmbedding block u).right • i = i :=
    degreeFourSylowCore_fixes_blocks block P S a i
  have haction : e (C • v, i) = u • x := by
    have he := ActualBlockWreathEmbedding.productEquiv_equivariant
      block.map block.map_equivariant block.base u (v, i)
    change e ((ambientEmbedding block u) • (v, i)) = u • x at he
    simpa only [PermutationalWreathProduct.smul_def, htop] using he
  have hax : a • x ≠ x := by
    intro he
    have he' : e (C • v, i) = e (v, i) := haction.trans he
    exact hv (congrArg Prod.fst (e.injective he'))
  let K := degreeFourSylowCore block P S
  letI : Nontrivial (MulAction.orbit K x) := ⟨⟨
    ⟨a • x, MulAction.mem_orbit x a⟩,
    ⟨x, MulAction.mem_orbit_self x⟩,
    fun he => hax (congrArg Subtype.val he)⟩⟩
  have hlarge : 1 < Nat.card (MulAction.orbit K x) :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  obtain ⟨n, hn⟩ := (S.isPGroup'.to_subgroup K).card_orbit x
  have hnpos : 1 ≤ n := by
    by_contra h
    have hz : n = 0 := by omega
    rw [hn, hz, pow_zero] at hlarge
    omega
  refine ⟨x, hx, ?_⟩
  rw [hn]
  simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 3) hnpos

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
