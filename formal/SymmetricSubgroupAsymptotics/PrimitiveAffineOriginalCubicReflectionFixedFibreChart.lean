import SymmetricSubgroupAsymptotics.PrimitiveAffineOriginalCubicFixedFibreChart
import SymmetricSubgroupAsymptotics.CubicPhysicalReflectionGauge

/-! Simultaneous Singer/reflection coordinates on the literal fixed
physical fibre of the actual cubic normalizer lift. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinaryFourBlockAugmentation

theorem originalCubicReflectionFixedFibreChart
    {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre] (hr : Nat.card block.Fibre = 4)
    (i : block.Points) (s g : preE7NonPairAction w U)
    (hsi : s • i = i) (hgi : g • i = i)
    (hs : s^3 = 1) (hne : QuotientGroup.mk' (E block P) s ≠ 1)
    (hg : g^2 = 1) (hgs : g*s*g⁻¹ = s⁻¹)
    (hlocal : Function.Injective (binaryAffineStabilizerComponent block P i)) :
    ∃ a : Local ≃ originalBlockFibre block.map i,
      (∀ v, (a (localCycle v)).1 = s • (a v).1) ∧
      ∀ v, (a (BinaryFourLocalCubicPointGauge.reflection v)).1 = g • (a v).1 := by
  let H := MulAction.stabilizer (preE7NonPairAction w U) i
  letI : MulAction H (originalBlockFibre block.map i) := {
    smul h x := ⟨h.1 • x.1,by
      rw [block.map_equivariant,x.2]
      exact h.2⟩
    one_smul x := Subtype.ext (one_smul _ _)
    mul_smul h k x := Subtype.ext (mul_smul _ _ _) }
  let sh : H := ⟨s,hsi⟩
  let gh : H := ⟨g,hgi⟩
  have hgh : gh^2 = 1 := Subtype.ext hg
  have hconj : gh*sh*gh⁻¹ = sh⁻¹ := Subtype.ext hgs
  obtain ⟨a,ha⟩ := originalCubicFixedFibreChart block P hr i s hsi hs hne hlocal
  have has : ∀ v, a (localCycle v) = sh • a v := by
    intro v
    apply Subtype.ext
    exact ha v
  obtain ⟨b,hbs,hbg⟩ := CubicPhysicalReflectionGauge.exists_gauge sh gh hgh hconj a has
  exact ⟨b,(fun v => congrArg Subtype.val (hbs v)),
    fun v => congrArg Subtype.val (hbg v)⟩

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
