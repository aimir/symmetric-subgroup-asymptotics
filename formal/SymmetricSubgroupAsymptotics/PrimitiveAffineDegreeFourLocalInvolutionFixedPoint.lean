import SymmetricSubgroupAsymptotics.FourPointRegularBinaryInvolution
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourNonzeroCore

/-! Every actual degree-four component involution outside the literal
translation kernel has an actual fixed fibre point. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

theorem degreeFourLocalInvolutionFixedPoint
    {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre] (hr : Nat.card block.Fibre = 4)
    (g : block.Component) (hg : g^2=1) (hne : localMap block P g ≠ 1) :
    ∃ x : block.Fibre, g • x = x := by
  classical
  by_contra h
  have hgf : ∀ x : block.Fibre, g • x ≠ x := by simpa using h
  letI : IsMulCommutative P.V := P.isMulCommutative (primitive block)
  have hV2 : ∀ v : P.V, v^2=1 := by
    intro v
    apply (chart block P).equiv.injective
    apply Multiplicative.toAdd.injective
    simp only [map_pow,map_one,toAdd_pow,toAdd_one]
    change 2 • ((chart block P).equiv v).toAdd = 0
    rw [← (degreeFour_translationDimension block P hr).1]
    exact ZModModule.char_nsmul_eq_zero P.p _
  let b := (Finite.equivFinOfCardEq hr).trans BinaryFourLocalCubicPointGauge.pointEquiv
  have hmem : g ∈ P.V := FourPointRegularBinaryInvolution.mem_regular P.V b
    (origin block) (P.regular (origin block))
    (fun v x hv => P.eq_one_of_smul_eq x v hv) hV2 g hg hgf
  apply hne
  apply MonoidHom.mem_ker.mp
  rw [localMap_ker block P]
  exact hmem

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
