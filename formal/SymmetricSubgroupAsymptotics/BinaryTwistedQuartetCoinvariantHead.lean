import SymmetricSubgroupAsymptotics.BinaryTwistedQuartetOutsideRadicalHead

/-! One cubic slot in EVERY actual V4-coinvariant quotient of EVERY
invariant binary subspace of the cubic-twisted quartet representation.
This is the translation half of original-N cubic-type sharing. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryTwistedQuartetCoinvariantHead
open BinaryTwistedQuartetPolynomial (Bit)
open BinaryTwistedQuartetLoewyCoordinates
open BinaryTwistedQuartetLoewyAugmentations

theorem nontrivial_rank_le_two (W : Submodule Bit Space)
    (hcycle : ∀ v, v∈W → cycleAction v∈W)
    (hflip : ∀ v, v∈W → flipAction v∈W)
    (hsecond : ∀ v, v∈W → secondFlip v∈W)
    {Q : Type} [AddCommGroup Q] [Module Bit Q]
    (q : W →ₗ[Bit] Q) (hq : Function.Surjective q) (T : Module.End Bit Q)
    (hinter : ∀ v : W, q ⟨cycleAction v,hcycle v v.property⟩=T (q v))
    (hqflip : ∀ v : W, q ⟨flipAction v,hflip v v.property⟩=q v)
    (hqsecond : ∀ v : W, q ⟨secondFlip v,hsecond v v.property⟩=q v) :
    Module.finrank Bit (LinearMap.range (T+T^2))≤2 := by
  by_cases hrad : ∀ v, v∈W → sumBlocks v=0
  · exact BinaryTwistedQuartetCoinvariantRadicalHead.nontrivial_rank_le_two
      W hcycle hflip hsecond hrad q T hinter hqflip hqsecond hq
  · push_neg at hrad
    obtain ⟨v,hv,hnon⟩ := hrad
    have hd := BinaryTwistedQuartetOutsideRadicalHead.rank_le_two
      W hcycle hflip hsecond q T hinter hqflip hqsecond hq ⟨v,hv⟩ hnon
    letI : FiniteDimensional Bit Q := FiniteDimensional.of_surjective q hq
    exact (T+T^2).range.finrank_le.trans hd

end SymmetricSubgroupAsymptotics.BinaryTwistedQuartetCoinvariantHead
