import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourOriginalCubicSylow
import SymmetricSubgroupAsymptotics.CubicSylowGenerator
import SymmetricSubgroupAsymptotics.CubicFourPointActionGauge
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreTopEquiv

/-! Choose the actual original Sylow, its actual cubic generator and the
four-block point chart. The block permutation is proved nonidentity using
the original zero-core quotient, not assumed as a chart certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

local instance originalCubicBlockGaugePrimeThree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem degreeFourOriginalCubicBlockGauge
    {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre] {C : Type} [Group C]
    (e : DegreeFourComplementQuotient block P ≃* C)
    (hcard : Nat.card C = 12 ∨ Nat.card C = 24)
    (hr : Nat.card block.Fibre = 4) (hs : Nat.card block.Points = 4)
    (hD : degreeFourTernaryCore block P = ⊥) :
    ∃ S : Sylow 3 (preE7NonPairAction w U), ∃ s : preE7NonPairAction w U,
      ∃ d : block.Points ≃ Fin 4,
        (S : Subgroup (preE7NonPairAction w U)) = Subgroup.zpowers s ∧
        s^3 = 1 ∧ s ≠ 1 ∧
        ∀ i : block.Points, d (s • i) = BinaryFourCubicNormalizerPointShapes.blockCycle (d i) := by
  let S : Sylow 3 (preE7NonPairAction w U) := default
  have hS := degreeFourOriginalCubicSylow_card block P e hr hcard S
  obtain ⟨s,hgen,hcube,hne⟩ := CubicSylowGenerator.exists_generator S hS
  have hsS : s ∈ (S : Subgroup (preE7NonPairAction w U)) := by
    rw [hgen]
    exact Subgroup.mem_zpowers s
  have hact : MulAction.toPermHom (preE7NonPairAction w U) block.Points s ≠ 1 := by
    intro h
    let q := QuotientGroup.mk' (E block P) s
    let et := degreeFourZeroCoreTopEquiv block P hr hD
    have ht : et q = 1 := by
      apply Subtype.ext
      change block.topMap s = 1
      exact h
    have hq : q = 1 := et.injective (ht.trans et.map_one.symm)
    have hf : degreeFourPhysicalCanonicalMap block P e s = 1 := by
      change e q = 1
      rw [hq,e.map_one]
    have hx : (⟨s,hsS⟩ : S) = 1 :=
      degreeFourOriginalCubicSylow_injective block P e hr S (by
        change degreeFourPhysicalCanonicalMap block P e s =
          degreeFourPhysicalCanonicalMap block P e 1
        rw [hf,map_one])
    exact hne (congrArg Subtype.val hx)
  obtain ⟨d,hd⟩ := CubicFourPointActionGauge.exists_gauge hs s hcube hact
  exact ⟨S,s,d,hgen,hcube,hne,hd⟩

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
