import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourSixteenDynamicInnerBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourSixteenStructuralReduction

/-! Transfer the exhaustive dynamic inner bounds through the same original
sixteen-point chart, retaining every outer normal axis and local twist. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

private theorem dynamic_head_at
    {p : ℕ} [Fact p.Prime] {X : Type} [Finite X]
    {S : Subgroup (Equiv.Perm X)} (C : SixteenPointNonPairOriginalChart S)
    (D : DegreeFourSixteenDynamicInnerBounds C.index) (hp : p=2)
    {L V : Type} [Group L] [Finite L] [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V]
    (x : X) (f : MulAction.stabilizer S x →* L) (hf : Function.Surjective f)
    (rho : Representation (ZMod p) L V) (hL : Nat.card L=3 ∨ Nat.card L=6)
    (hdim : Module.finrank (ZMod p) V=2) (hrho : Function.Injective rho)
    (B : Subrepresentation (Representation.coind (MulAction.stabilizer S x).subtype (rho.comp f))) :
    Module.finrank (ZMod p) (B.toRepresentation.IntertwiningMap
      (Representation.trivial (ZMod p) S (ZMod p))) ≤ D.externalSlots := by
  subst p
  apply C.uniform_head_le x f rho D.externalSlots _ B
  intro A
  exact D.external (C.points x) (C.localMap x f) (C.localMap_surjective x f hf)
    rho hL hdim hrho A

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre) [Nontrivial block.Fibre]
local instance sixteenZeroInnerPrime : Fact P.p.Prime := (chart block P).primeFact

def degreeFourZeroCoreSixteenZeroInnerBounds
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hr : Nat.card block.Fibre=4) (hD : degreeFourTernaryCore block P=⊥)
    (C : SixteenPointNonPairOriginalChart block.Top) {b : Fin 16}
    (inner : OriginalMinimalBlock (A := preE7NonPairAction 16 C.index) b)
    (R : PrimitiveAffineProfile inner.Component inner.Fibre) [Nontrivial inner.Fibre]
    (hinner : Nat.card inner.Fibre=4) (hpoints : Nat.card inner.Points=4)
    (hinnerD : degreeFourTernaryCore inner R=⊥) :
    DegreeFourZeroCoreFiniteFrameBounds block P 10 := by
  let D := degreeFourSixteenDynamicInnerBounds inner R hMN hinner hpoints hinnerD
  let i : block.Points := C.points.symm 0
  apply DegreeFourZeroCoreFiniteFrameBounds.ofTopCoinduced block P hr hD i
    D.relativeSlots D.externalSlots 10 D.sum_le
  · intro N _
    exact C.relative_head_le 2 D.relativeSlots D.relative N
  · intro B
    exact dynamic_head_at C D (degreeFour_profilePrime_eq_two block P hr) i
      (degreeFourZeroCoreTopStabilizerLocalMap block P hr hD i)
      (degreeFourZeroCoreTopStabilizerLocalMap_surjective block P hr hD i)
      (binaryAffineLocalLinearRepresentation block P).ρ
      (degreeFourZeroCoreTopStabilizerLocalTarget_card block P hr)
      (by change (chart block P).d=2; exact (degreeFour_translationDimension block P hr).2)
      (binaryAffineLocalLinearRepresentation_injective block P) B

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
