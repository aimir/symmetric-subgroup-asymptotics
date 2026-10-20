import SymmetricSubgroupAsymptotics.BinaryPairTrivialKernelFrameBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourPairFrameSource

/-! Return the faithful-pair-action moving-orbit bound to the unchanged
degree-four affine profile. The original local map and every original
normal quotient remain those of the profile. The finite rank-two statement
on the actual eight-point top is the only remaining catalogue obligation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics

namespace BinaryPairFrame

theorem originalFrame_head_le_eight_at
    {p : ℕ} [Fact p.Prime] {X I C V : Type}
    [Finite X] [Finite I] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] [Group C] [Finite C]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (F : BinaryPairFrame U I) (hp : p = 2) (hI : Nat.card I = 8) (x : X)
    (f : MulAction.stabilizer U x →* C) (hf : Function.Surjective f)
    (rho : Representation (ZMod p) C V)
    (hC : Nat.card C = 3 ∨ Nat.card C = 6)
    (hdim : Module.finrank (ZMod p) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer U x).subtype (rho.comp f))) :
    Module.finrank (ZMod p)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod p) U (ZMod p))) ≤ 8 := by
  subst p
  exact BinaryPairTernaryOrbitHead.original_head_le_eight F hI x f hf rho hC hdim hrho B

end BinaryPairFrame

namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
  (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

local instance degreeFourPairTrivialKernelSource_profilePrimeFact : Fact P.p.Prime := (chart block P).primeFact
local instance : MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive

/-- The actual trivial-pair-kernel structural branch, with the original
profile as output. The frame contribution8 is proved by Sylow geometry. -/
def degreeFourZeroCoreSixteenPairKernelTrivialBounds
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    {I : Type} [Finite I] (F : BinaryPairFrame block.Top I)
    (hker : F.top.ker = ⊥) (hcard : Nat.card I = 8) (x : block.Points)
    (htop : ∀ (N : Subgroup F.top.range) [N.Normal],
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ 2) :
    DegreeFourZeroCoreFiniteFrameBounds block P 10 := by
  apply DegreeFourZeroCoreFiniteFrameBounds.ofTopCoinduced block P hr hD x
    2 8 10 (by decide)
  · intro N _
    exact F.trivialKernel_relativeHead_le_two hker htop N
  · intro B
    have hdim : Module.finrank (ZMod P.p) (chart block P).V = 2 := by
      change (chart block P).d = 2
      exact (degreeFour_translationDimension block P hr).2
    exact F.originalFrame_head_le_eight_at (degreeFour_profilePrime_eq_two block P hr)
      hcard x (degreeFourZeroCoreTopStabilizerLocalMap block P hr hD x)
      (degreeFourZeroCoreTopStabilizerLocalMap_surjective block P hr hD x)
      (binaryAffineLocalLinearRepresentation block P).ρ
      (degreeFourZeroCoreTopStabilizerLocalTarget_card block P hr) hdim
      (binaryAffineLocalLinearRepresentation_injective block P) B

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
