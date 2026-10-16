import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop1NormalizerHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTopRelativeHeads
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourPairFrameSource
import SymmetricSubgroupAsymptotics.PermutationStabilizerTransport

/-! The actual original degree-four frame above historical eight-point
top1. Both bounds are obtained structurally from checked quotient socles
and one double-orbit evaluation, without historical native module data. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics

namespace PrimitiveAffineEightTop1NormalizerHead

theorem literal_head_le_two_at {p : ℕ} [Fact p.Prime] (hp : p = 2)
    {L V : Type} [Group L] [Finite L]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (f : literalStabilizer →* L) (hf : Function.Surjective f)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (rho : Representation (ZMod p) L V)
    (hdim : Module.finrank (ZMod p) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation (Representation.coind literalStabilizer.subtype (rho.comp f))) :
    Module.finrank (ZMod p)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod p) Literal (ZMod p))) ≤ 2 := by
  subst p
  exact literal_head_le_two f hf hL rho hdim hrho B

end PrimitiveAffineEightTop1NormalizerHead

namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
  (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

local instance degreeFourEightTop1Source_profilePrimeFact : Fact P.p.Prime := (chart block P).primeFact

def degreeFourZeroCoreEightTop1Bounds
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (points : block.Points ≃ Fin 8) (g : Equiv.Perm (Fin 8))
    (matched : MulAut.conj g • relabelSubgroup points block.Top =
      PrimitiveAffineEightTop1NormalizerHead.Literal) :
    DegreeFourZeroCoreFiniteFrameBounds block P 5 := by
  let T := PrimitiveAffineEightTop1NormalizerHead.Literal
  let L := PrimitiveAffineEightTop1NormalizerHead.literalStabilizer
  let eG := PermutationStabilizerTransport.groupEquiv block.Top T points g matched
  let x := (PermutationStabilizerTransport.pointEquiv points g).symm 0
  let H := MulAction.stabilizer block.Top x
  let eH : H ≃* L := PermutationStabilizerTransport.stabilizerEquiv
    block.Top T points g matched 0
  let f := degreeFourZeroCoreTopStabilizerLocalMap block P hr hD x
  let f' := f.comp eH.symm.toMonoidHom
  let rho := (binaryAffineLocalLinearRepresentation block P).ρ
  let eV : Representation.Equiv (rho.comp f) ((rho.comp f').comp eH.toMonoidHom) :=
    Representation.Equiv.mk (LinearEquiv.refl (ZMod P.p) (chart block P).V) (by
      intro h
      ext v
      change rho (f h) v = rho (f (eH.symm (eH h))) v
      rw [eH.symm_apply_apply])
  apply DegreeFourZeroCoreFiniteFrameBounds.ofTopCoinduced block P hr hD x
    2 2 5 (by decide)
  · intro N _
    exact PrimitiveAffineEightTopRelativeHeads.relativeHead_le_two_of_equiv 2 0 eG N
  · intro B
    have hdim : Module.finrank (ZMod P.p) (chart block P).V = 2 := by
      change (chart block P).d = 2
      exact (degreeFour_translationDimension block P hr).2
    exact CoinducedGroupLocalTransport.uniform_head_le H L eG eH (fun _ => rfl)
      (rho.comp f) (rho.comp f') eV 2
      (fun A => PrimitiveAffineEightTop1NormalizerHead.literal_head_le_two_at
        (degreeFour_profilePrime_eq_two block P hr) f'
        ((degreeFourZeroCoreTopStabilizerLocalMap_surjective block P hr hD x).comp
          eH.symm.surjective)
        (degreeFourZeroCoreTopStabilizerLocalTarget_card block P hr) rho hdim
        (binaryAffineLocalLinearRepresentation_injective block P) A) B

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
