import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourTernaryFibreOrbit
import SymmetricSubgroupAsymptotics.SylowThreeMovingOrbit
import SymmetricSubgroupAsymptotics.BinaryCoinducedLargeOrbitOriginalHead

/-! In the nonzero-core four-by-four branch with nonbinary block top,
every original Sylow-three subgroup has a nine-point orbit. This proves
the six-dimensional head estimate on every original local-epi frame,
without any finite rank, head, subgroup or module certificate. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]

theorem degreeFourNonzeroFourBlock_largeSylowOrbit
    (hr : Nat.card block.Fibre = 4) (hs : Nat.card block.Points = 4)
    (hD : degreeFourTernaryCore block P ≠ ⊥) (hTop : ¬ IsPGroup 2 block.Top)
    (S : Sylow 3 (preE7NonPairAction w U)) :
    ∃ x : Fin w, 9 ≤ Nat.card (MulAction.orbit S x) := by
  have hthree : 3 ∣ Nat.card block.Top :=
    three_dvd_card_four_point_nonbinary block.Top hs hTop
  obtain ⟨i, hi⟩ := sylow_three_exists_moving_orbit (I := block.Points)
    block.topMap.rangeRestrict block.topMap.rangeRestrict_surjective
    (fun _ _ => rfl) hthree S
  obtain ⟨x, hx, hKx⟩ := degreeFourSylowCore_exists_fibre_orbit block P S hr hD i
  have hblock : 3 ≤ Nat.card (MulAction.orbit S (block.map x)) := hx.symm ▸ hi
  have hprod := orbit_card_ge_block_mul_fibre block.map
    (fun (g : S) y => block.map_equivariant (g : preE7NonPairAction w U) y)
    (degreeFourSylowCore block P S) x
    (fun k => degreeFourSylowCore_fixes_blocks block P S k (block.map x))
  exact ⟨x, (Nat.mul_le_mul hblock hKx).trans hprod⟩

/-- This theorem quantifies over the actual external local epimorphism;
it does not identify it with the internal affine complement. -/
theorem degreeFourNonzeroFourBlock_original_head_le_six
    (hr : Nat.card block.Fibre = 4) (hs : Nat.card block.Points = 4)
    (hD : degreeFourTernaryCore block P ≠ ⊥) (hTop : ¬ IsPGroup 2 block.Top)
    {L V : Type} [Group L] [Finite L] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (x : Fin w)
    (f : MulAction.stabilizer (preE7NonPairAction w U) x →* L)
    (hf : Function.Surjective f) (rho : Representation (ZMod 2) L V)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer (preE7NonPairAction w U) x).subtype
        (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) (preE7NonPairAction w U) (ZMod 2))) ≤ 6 := by
  let S : Sylow 3 (preE7NonPairAction w U) := Classical.choice inferInstance
  obtain ⟨y, hy⟩ := degreeFourNonzeroFourBlock_largeSylowOrbit block P hr hs hD hTop S
  have hw : Nat.card (Fin w) = 16 := by
    have h := block.degree_product
    rw [hr, hs] at h
    exact h.symm
  exact BinaryCoinducedLargeOrbitHead.head_le_six_on_points x S hw y hy
    f hf rho hL hdim hrho B

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
