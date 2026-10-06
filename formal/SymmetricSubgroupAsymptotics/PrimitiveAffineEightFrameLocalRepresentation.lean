import SymmetricSubgroupAsymptotics.BinaryPlaneOrderThreeRepresentation
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameFullFrameInduced
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFramePointedTopMatch

/-!
# Reusable local representation match for eight-block frame rows

Every degree-four zero-core local quotient has order three or six.  Its
faithful binary plane is therefore unique up to representation equivalence:
the order-three case is cyclic, while the order-six case is `GL₂(2)` and
all of its automorphisms are inner.  This file packages that fact at the
literal pointed-row boundary, so individual finite rows only retain their
checked local matrix homomorphism and its injectivity.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

local instance localRepresentationPrimeFact : Fact P.p.Prime :=
  (chart block P).primeFact

/-- Characteristic-transported form of binary-plane uniqueness for either
allowed local quotient order. -/
noncomputable def binaryPlaneRepresentationEquiv_of_card_three_or_six_at
    {p : ℕ} [Fact p.Prime]
    {G V W : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    [AddCommGroup W] [Module (ZMod p) W] [FiniteDimensional (ZMod p) W]
    (hp : p = 2)
    (rho : Representation (ZMod p) G V)
    (sigma : Representation (ZMod p) G W)
    (hG : Nat.card G = 3 ∨ Nat.card G = 6)
    (hV : Module.finrank (ZMod p) V = 2)
    (hW : Module.finrank (ZMod p) W = 2)
    (hrho : Function.Injective rho)
  (hsigma : Function.Injective sigma) :
    rho.Equiv sigma := by
  subst p
  by_cases h3 : Nat.card G = 3
  · exact binaryPlaneRepresentationEquiv_of_card_three
      rho sigma h3 hV hW hrho hsigma
  · exact binaryPlaneRepresentationEquiv_of_card_six
      rho sigma (hG.resolve_left h3) hV hW hrho hsigma

/-- Restrict a representation equivalence along a group homomorphism. -/
noncomputable def representationEquivComp
    {k G K V W : Type} [Semiring k] [Group G] [Group K]
    [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W]
    {rho : Representation k G V} {sigma : Representation k G W}
    (e : Representation.Equiv rho sigma) (f : K →* G) :
    Representation.Equiv (rho.comp f) (sigma.comp f) :=
  Representation.Equiv.mk e.toLinearEquiv
    (fun x ↦ e.isIntertwining' (f x))

/-- A faithful checked action of the selected local quotient on a binary
plane is equivalent to the actual affine local action. -/
noncomputable def pointedLocalBinaryPlaneEquiv
    {ModelGroup : Type} [Group ModelGroup]
    {topMatch : DegreeFourZeroCoreEightLiteralTopMatch block ModelGroup}
    {hr : Nat.card block.Fibre = 4}
    {hD : degreeFourTernaryCore block P = ⊥}
    {literalPoint : Fin 8}
    (L : DegreeFourZeroCoreEightPointedLocalMatch
      block P topMatch hr hD literalPoint)
    (sigma : Representation (ZMod P.p) L.ModelLocalGroup
      (Fin 2 → ZMod P.p))
    (hsigma : Function.Injective sigma) :
    (binaryAffineLocalLinearRepresentation block P).ρ.Equiv
      (sigma.comp L.targetEquiv.toMonoidHom) := by
  have hp : P.p = 2 := degreeFour_profilePrime_eq_two block P hr
  have hV : Module.finrank (ZMod P.p) (chart block P).V = 2 := by
    change (chart block P).d = 2
    exact (degreeFour_translationDimension block P hr).2
  have hrho : Function.Injective
      (binaryAffineLocalLinearRepresentation block P).ρ :=
    binaryAffineLocalLinearRepresentation_injective block P
  exact binaryPlaneRepresentationEquiv_of_card_three_or_six_at hp
    (binaryAffineLocalLinearRepresentation block P).ρ
    (sigma.comp L.targetEquiv.toMonoidHom)
    (by
      rcases L.local_card with h3 | h6
      · exact Or.inl (by
          simpa only [Nat.card_congr L.targetEquiv.toEquiv] using h3)
      · exact Or.inr (by
          simpa only [Nat.card_congr L.targetEquiv.toEquiv] using h6))
    hV (by simp) hrho (hsigma.comp L.targetEquiv.injective)

/-- Restrict the quotient-level binary-plane equivalence to the actual
point stabilizer used by the induced full-frame coordinates. -/
noncomputable def pointedInducedLocalEquiv
    {ModelGroup : Type} [Group ModelGroup]
    {topMatch : DegreeFourZeroCoreEightLiteralTopMatch block ModelGroup}
    {hr : Nat.card block.Fibre = 4}
    {hD : degreeFourTernaryCore block P = ⊥}
    {literalPoint : Fin 8}
    (L : DegreeFourZeroCoreEightPointedLocalMatch
      block P topMatch hr hD literalPoint)
    (sigma : Representation (ZMod P.p) L.ModelLocalGroup
      (Fin 2 → ZMod P.p))
    (hsigma : Function.Injective sigma) :
    (fullFrameInducedLocalRepresentation block P
        (DegreeFourZeroCoreEightLiteralTopMatch.pointOver
          (block := block) topMatch literalPoint)).Equiv
      (sigma.comp
        (L.targetEquiv.toMonoidHom.comp
          (binaryAffineStabilizerComponent block P
            (DegreeFourZeroCoreEightLiteralTopMatch.pointOver
              (block := block) topMatch literalPoint)))) :=
  representationEquivComp
    (pointedLocalBinaryPlaneEquiv block P L sigma hsigma)
    (binaryAffineStabilizerComponent block P
      (DegreeFourZeroCoreEightLiteralTopMatch.pointOver
        (block := block) topMatch literalPoint))

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
