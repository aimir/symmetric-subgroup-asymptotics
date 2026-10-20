import SymmetricSubgroupAsymptotics.SixteenPointNonPairFrameTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourNonzeroFourBlockFrame
import SymmetricSubgroupAsymptotics.PrimitiveAffineZeroCoreCoinducedConsumer

/-! The internal four-by-four branch with nonzero ternary core gives an
actual ten-slot frame for the outer zero-core degree-four profile. Both
normal ranks and local heads are transported through the original point
chart. All local epimorphisms remain the original outer stabilizer maps. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

theorem nonzeroInnerFourBlock_head_le_six_at
    {p : ℕ} [Fact p.Prime] {X : Type} [Finite X]
    {S : Subgroup (Equiv.Perm X)} (C : SixteenPointNonPairOriginalChart S)
    {b : Fin 16}
    (inner : OriginalMinimalBlock (A := preE7NonPairAction 16 C.index) b)
    (R : PrimitiveAffineProfile inner.Component inner.Fibre) [Nontrivial inner.Fibre]
    (hp : p = 2) (hr : Nat.card inner.Fibre = 4) (hs : Nat.card inner.Points = 4)
    (hD : degreeFourTernaryCore inner R ≠ ⊥)
    {L V : Type} [Group L] [Finite L] [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V]
    (x : X) (f : MulAction.stabilizer S x →* L) (hf : Function.Surjective f)
    (rho : Representation (ZMod p) L V) (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (hdim : Module.finrank (ZMod p) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer S x).subtype (rho.comp f))) :
    Module.finrank (ZMod p)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod p) S (ZMod p))) ≤ 6 := by
  subst p
  apply C.uniform_head_le x f rho 6 _ B
  intro A
  by_cases hTop : IsPGroup 2 inner.Top
  · exact (degreeFourFourBlockBinaryTop_original_head_le_four inner hr hs hTop
      (C.points x) (C.localMap x f) (C.localMap_surjective x f hf)
      rho hL hdim hrho A).trans (by decide)
  · exact degreeFourNonzeroFourBlock_original_head_le_six inner R hr hs hD hTop
      (C.points x) (C.localMap x f) (C.localMap_surjective x f hf)
      rho hL hdim hrho A

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]

local instance innerNonzeroSource_prime : Fact P.p.Prime := (chart block P).primeFact

/-- The only hypotheses beyond published inputs are the actual inner
geometry and its nonzero ternary core. No normal-rank or module bound is
left as a certificate field. -/
def degreeFourZeroCoreSixteenNonzeroInnerBounds
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (C : SixteenPointNonPairOriginalChart block.Top)
    {b : Fin 16}
    (inner : OriginalMinimalBlock (A := preE7NonPairAction 16 C.index) b)
    (R : PrimitiveAffineProfile inner.Component inner.Fibre) [Nontrivial inner.Fibre]
    (hinner : Nat.card inner.Fibre = 4) (hpoints : Nat.card inner.Points = 4)
    (hinnerD : degreeFourTernaryCore inner R ≠ ⊥) :
    DegreeFourZeroCoreFiniteFrameBounds block P 10 := by
  let i : block.Points := C.points.symm 0
  apply DegreeFourZeroCoreFiniteFrameBounds.ofTopCoinduced block P hr hD i
    4 6 10 (by decide)
  · intro N _
    apply C.relative_head_le 2 4 _ N
    intro M _
    exact degreeFourFourBlockNonzero_binary_relative_head_le_four inner R
      hMN hClifford hTraceyPerm hinner hpoints hinnerD M
  · intro B
    exact nonzeroInnerFourBlock_head_le_six_at C inner R
      (degreeFour_profilePrime_eq_two block P hr) hinner hpoints hinnerD i
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
