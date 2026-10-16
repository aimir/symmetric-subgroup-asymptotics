import SymmetricSubgroupAsymptotics.BinaryFourCanonicalNaturalChart
import SymmetricSubgroupAsymptotics.CoinducedGroupLocalEquiv
import SymmetricSubgroupAsymptotics.BinaryPlaneOrderThreeRepresentation

/-! Identify an original A4 coinduced binary plane with the actual
canonical eight-coordinate module. Only the exact ambient/stabilizer maps
and the original faithful local plane are inputs; no bound is assumed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourA4OriginalInducedChart

open BinaryFourBlockAugmentation BinaryFourCanonicalInducedChart

theorem canonicalLocal_injective : Function.Injective localRepresentation := by
  intro h k heq
  apply stabilizerTernary_injective
  have detect : ∀ z w : Ternary,
      localLinear z ![1, 0] = localLinear w ![1, 0] → z = w := by decide +kernel
  apply detect
  exact congrArg (fun L : _root_.Module.End Scalar Local => L ![1, 0]) heq

variable {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [_root_.Module Scalar V] [FiniteDimensional Scalar V]
    (H : Subgroup G) (eG : G ≃* Complement) (eH : H ≃* stabilizer)
    (commutes : ∀ h : H, eG (h : G) = (eH h : Complement))
    (rho : Representation Scalar H V)
    (hdim : _root_.Module.finrank Scalar V = 2) (hrho : Function.Injective rho)

private theorem sourceLocal_card (eH' : H ≃* stabilizer) : Nat.card H = 3 := by
  rw [Nat.card_congr eH'.toEquiv, Nat.card_congr stabilizerTernaryEquiv.toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Ternary ≃ ZMod 3), Nat.card_zmod]

def localPlaneEquiv : rho.Equiv (localRepresentation.comp eH.toMonoidHom) :=
  binaryPlaneRepresentationEquiv_of_card_three rho
    (localRepresentation.comp eH.toMonoidHom) (sourceLocal_card H eH) hdim
    (by rw [_root_.Module.finrank_pi]; simp)
    hrho (canonicalLocal_injective.comp eH.injective)

/-- Exact original coinduced chart, retaining the ambient pullback through
its given group equivalence and the same faithful local-plane action. -/
def originalCoinducedChart : Representation.Equiv
    (Representation.coind H.subtype rho)
    (fullCoordinatesRepresentation.comp eG.toMonoidHom) := by
  let e₁ := CoinducedGroupLocalTransport.equivalence
    H stabilizer eG eH commutes rho localRepresentation
    (localPlaneEquiv H eH rho hdim hrho)
  let e₂ : Representation.Equiv
      ((Representation.coind stabilizer.subtype localRepresentation).comp eG.toMonoidHom)
      (fullCoordinatesRepresentation.comp eG.toMonoidHom) := {
    toLinearEquiv := fullCoinducedChart.symm.toLinearEquiv
    isIntertwining' := fun g => fullCoinducedChart.symm.isIntertwining' (eG g) }
  exact e₁.trans e₂

/-- The original local epimorphism suffices: the actual A4 point
stabilizer has order three, so its local order-three/six target forces an
isomorphism. This discharges faithfulness on the original stabilizer. -/
def originalCoinducedChart_of_local_epi
    {L : Type} [Group L] [Finite L]
    (f : H →* L) (hf : Function.Surjective f)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (theta : Representation Scalar L V)
    (htheta : Function.Injective theta) : Representation.Equiv
    (Representation.coind H.subtype (theta.comp f))
    (fullCoordinatesRepresentation.comp eG.toMonoidHom) := by
  have hH : Nat.card H = 3 := sourceLocal_card H eH
  have hle : Nat.card L ≤ 3 := by
    simpa only [hH] using Nat.card_le_card_of_surjective f hf
  have htarget : Nat.card L = 3 := by omega
  have hfi : Function.Injective f :=
    ((Nat.bijective_iff_surjective_and_card f).mpr ⟨hf, hH.trans htarget.symm⟩).1
  exact originalCoinducedChart H eG eH commutes (theta.comp f) hdim (htheta.comp hfi)

end SymmetricSubgroupAsymptotics.BinaryFourA4OriginalInducedChart

end
