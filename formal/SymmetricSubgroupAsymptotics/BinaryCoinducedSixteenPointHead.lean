import SymmetricSubgroupAsymptotics.BinaryPairTernaryOrbitHead

/-! Every actual binary-plane coinduced frame on sixteen original points
has head at most ten: moving ternary orbits each consume three points.
The original stabilizer, local epimorphism and twist are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCoinducedSixteenPointHead
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem head_le_ten_on_points
    {G X L V : Type} [Group G] [Finite G] [MulAction G X]
    [MulAction.IsPretransitive G X] [Finite X]
    [Group L] [Finite L] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (x : X) (hX : Nat.card X = 16)
    (f : MulAction.stabilizer G x →* L) (hf : Function.Surjective f)
    (rho : Representation (ZMod 2) L V) (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer G x).subtype (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2))) ≤ 10 := by
  let P : Sylow 3 G := default
  let H := MulAction.stabilizer G x
  have hcoset : Nat.card (G ⧸ H) = 16 :=
    (Nat.card_congr (BinaryPairTernaryOrbitHead.pointCosetEquiv x)).trans hX
  letI : Finite (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) :=
    Finite.of_injective (inducedDoubleCosetToOrbit H (P : Subgroup G))
      (inducedDoubleCosetToOrbit_injective H (P : Subgroup G))
  letI : Fintype (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) :=
    Fintype.ofFinite _
  have h := BinaryCoinducedSylowOrbitHead.subrepresentation_head_le_twice_moving
    H P f hf rho hL hdim hrho B
  rw [BinaryPairTernaryOrbitHead.movingDoubleCoset_card H P] at h
  have hcount := TernaryMovingOrbitCount.fixed_add_three_mul_moving_le
    P (G ⧸ H) P.isPGroup'
  omega

end SymmetricSubgroupAsymptotics.BinaryCoinducedSixteenPointHead
