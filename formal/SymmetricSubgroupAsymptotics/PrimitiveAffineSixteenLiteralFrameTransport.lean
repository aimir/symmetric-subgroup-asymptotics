import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenAllLiteralFrames
import SymmetricSubgroupAsymptotics.PermutationStabilizerTransport
import SymmetricSubgroupAsymptotics.CoinducedGroupLocalTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineZeroCoreCoinducedConsumer

/-! The twenty-two original literal frame estimates under an exact point
chart. Every original normal subgroup is mapped by the same ambient
isomorphism; the representation is pulled through its actual stabilizer
isomorphism. The chart itself remains a concrete correspondence datum,
not an assumed classification or frame-bound theorem. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineSixteenAllLiteralFrames

structure LiteralMatch {X : Type} (S : Subgroup (Equiv.Perm X)) where
  index : Fin 22
  points : X ≃ Fin 16
  conjugator : Equiv.Perm (Fin 16)
  matched : MulAut.conj conjugator • relabelSubgroup points S = top index

namespace LiteralMatch
variable {X : Type} [Finite X] {S : Subgroup (Equiv.Perm X)} (C : LiteralMatch S)

def sourcePoint : X := (C.points.trans C.conjugator).symm 0

def groupEquiv : S ≃* top C.index :=
  PermutationStabilizerTransport.groupEquiv S _ C.points C.conjugator C.matched

def stabilizerEquiv : MulAction.stabilizer S C.sourcePoint ≃*
    MulAction.stabilizer (top C.index) (0 : Fin 16) :=
  PermutationStabilizerTransport.stabilizerEquiv S _ C.points C.conjugator C.matched 0

include C in
theorem relative_head_le_two (N : Subgroup S) [N.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ 2 := by
  let M := N.map (groupEquiv C).toMonoidHom
  letI : M.Normal := Subgroup.Normal.map inferInstance _ C.groupEquiv.surjective
  rw [← (relativeCharacterAmbientCongr 2 C.groupEquiv N M rfl).finrank_eq]
  exact PrimitiveAffineSixteenAllLiteralFrames.relative_head_le_two C.index M

/-- The local source and its action are retained through the exact chart. -/
theorem head_le_eight {p : ℕ} [Fact p.Prime] (hp : p = 2)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (rho : Representation (ZMod p) (MulAction.stabilizer S C.sourcePoint) V)
    (hdim : Module.finrank (ZMod p) V = 2)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer S C.sourcePoint).subtype rho)) :
    Module.finrank (ZMod p)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod p) S (ZMod p)))
      ≤ 8 := by
  subst p
  let sigma : Representation (ZMod 2)
      (MulAction.stabilizer (top C.index) (0 : Fin 16)) V :=
    rho.comp C.stabilizerEquiv.symm.toMonoidHom
  let eV : Representation.Equiv rho (sigma.comp C.stabilizerEquiv.toMonoidHom) :=
    Representation.Equiv.mk (LinearEquiv.refl (ZMod 2) V) (by
      intro h
      apply LinearMap.ext
      intro v
      change rho h v = rho (C.stabilizerEquiv.symm (C.stabilizerEquiv h)) v
      rw [MulEquiv.symm_apply_apply])
  exact CoinducedGroupLocalTransport.uniform_head_le
    (MulAction.stabilizer S C.sourcePoint)
    (MulAction.stabilizer (top C.index) (0 : Fin 16))
    C.groupEquiv C.stabilizerEquiv (fun _ => rfl) rho sigma eV 8
    (fun A => PrimitiveAffineSixteenAllLiteralFrames.original_head_le_eight
      C.index 0 sigma hdim A) B

end LiteralMatch
end PrimitiveAffineSixteenAllLiteralFrames

namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]

local instance primitiveLiteralFrame_prime : Fact P.p.Prime := (chart block P).primeFact

/-- Populate the original frame consumer from the exact twenty-two-row
point chart. Its relative and local head bounds are proved internally. -/
def degreeFourZeroCoreSixteenPrimitiveLiteralBounds
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (C : PrimitiveAffineSixteenAllLiteralFrames.LiteralMatch block.Top) :
    DegreeFourZeroCoreFiniteFrameBounds block P 10 := by
  apply DegreeFourZeroCoreFiniteFrameBounds.ofTopCoinduced block P hr hD C.sourcePoint
    2 8 10 (by decide)
  · intro N _
    exact C.relative_head_le_two N
  · intro B
    apply C.head_le_eight (degreeFour_profilePrime_eq_two block P hr)
      (zeroCoreTopLocalRepresentation block P hr hD C.sourcePoint) _ B
    change (chart block P).d = 2
    exact (degreeFour_translationDimension block P hr).2

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
end
