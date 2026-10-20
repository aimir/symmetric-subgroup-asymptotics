import SymmetricSubgroupAsymptotics.OriginalTwoBlockPrimitiveFrame
import SymmetricSubgroupAsymptotics.PrimitiveAffineZeroCoreCoinducedConsumer

/-! Return the actual internal eight-point-component branch to the
original degree-four affine frame. The original quotient top has two
blocks, relative rank at most3 and coinduced head at most4. Every input
other than the fixed published canonical classification is actual
original geometry; no literal match or local capacity premise remains. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics

namespace OriginalMinimalBlock

theorem twoBlock_head_le_four_at
    {p : ℕ} [Fact p.Prime]
    {G X C V : Type} [Group G] [Finite G] [MulAction G X]
    [MulAction.IsPretransitive G X] [FaithfulSMul G X] [Finite X]
    [Group C] [Finite C] [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V]
    {x₀ : X} (D : OriginalMinimalBlock (A := G) x₀)
    (hp : p = 2) (hs : Nat.card D.Points = 2) (hX : Nat.card X = 16)
    (x : X) (f : MulAction.stabilizer G x →* C) (hf : Function.Surjective f)
    (rho : Representation (ZMod p) C V) (hC : Nat.card C = 3 ∨ Nat.card C = 6)
    (hdim : Module.finrank (ZMod p) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer G x).subtype (rho.comp f))) :
    Module.finrank (ZMod p)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod p) G (ZMod p))) ≤ 4 := by
  subst p
  letI : Nontrivial D.Points := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  exact BinaryTopNormalizerOrbitHead.head_le_four_on_points x hX
    D.topMap.rangeRestrict D.topMap.rangeRestrict_surjective (D.twoBlock_top_isPGroup hs)
    (fun _ _ => rfl) D.map D.map_equivariant f hf rho hC hdim hrho B

end OriginalMinimalBlock

namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
  (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

local instance twoBlockSource_prime : Fact P.p.Prime := (chart block P).primeFact
local instance twoBlockSource_transitive :
    MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive

def degreeFourZeroCoreSixteenTwoBlockPrimitiveBounds
    (published : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (hs : Nat.card block.Points = 16) (i : block.Points)
    (inner : OriginalMinimalBlock (A := block.Top) i)
    (hinner : Nat.card inner.Fibre = 8) :
    DegreeFourZeroCoreFiniteFrameBounds block P 10 := by
  have htwo : Nat.card inner.Points = 2 := by
    have h := inner.degree_product
    rw [hinner, hs] at h
    omega
  apply DegreeFourZeroCoreFiniteFrameBounds.ofTopCoinduced block P hr hD i
    3 4 10 (by decide)
  · intro N _
    exact inner.twoBlock_relativeHead_le htwo
      (inner.eightPoint_component_normal_singletons published hinner) N
  · intro B
    exact inner.twoBlock_head_le_four_at
      (degreeFour_profilePrime_eq_two block P hr) htwo hs i
      (degreeFourZeroCoreTopStabilizerLocalMap block P hr hD i)
      (degreeFourZeroCoreTopStabilizerLocalMap_surjective block P hr hD i)
      (binaryAffineLocalLinearRepresentation block P).ρ
      (degreeFourZeroCoreTopStabilizerLocalTarget_card block P hr)
      (by
        change (chart block P).d = 2
        exact (degreeFour_translationDimension block P hr).2)
      (binaryAffineLocalLinearRepresentation_injective block P) B

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
