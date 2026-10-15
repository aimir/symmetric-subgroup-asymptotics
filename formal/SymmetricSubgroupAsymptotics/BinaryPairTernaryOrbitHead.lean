import SymmetricSubgroupAsymptotics.BinaryPairTernaryFixedPoints
import SymmetricSubgroupAsymptotics.TernaryMovingOrbitCount
import SymmetricSubgroupAsymptotics.BinaryCoinducedSylowOrbitHead

/-! The eight-moving-coordinate head bound for an original sixteen-point
pair action. The original point stabilizer and its actual local epimorphism
are kept throughout. The geometric hypotheses are exactly an eight-pair
frame and transitivity; no orbit table or head-capacity premise remains. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPairTernaryOrbitHead

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

section CosetGeometry

variable {G X : Type} [Group G] [MulAction G X]
  [MulAction.IsPretransitive G X] (x : X)

/-- The actual transitive point action is its actual stabilizer coset action. -/
def pointCosetEquiv : (G ⧸ MulAction.stabilizer G x) ≃ X :=
  Equiv.ofBijective (MulAction.ofQuotientStabilizer G x)
    ⟨MulAction.injective_ofQuotientStabilizer G x, by
      intro y
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
      exact ⟨(g : G ⧸ MulAction.stabilizer G x), hg⟩⟩

theorem pointCosetEquiv_smul (g : G) (q : G ⧸ MulAction.stabilizer G x) :
    pointCosetEquiv x (g • q) = g • pointCosetEquiv x q :=
  MulAction.ofQuotientStabilizer_smul G x g q

def fixedPointCosetEquiv (P : Subgroup G) :
    MulAction.fixedPoints P (G ⧸ MulAction.stabilizer G x) ≃
      MulAction.fixedPoints P X :=
  (pointCosetEquiv x).subtypeEquiv (by
    intro q
    constructor
    · intro h p
      change (p : G) • pointCosetEquiv x q = pointCosetEquiv x q
      rw [← pointCosetEquiv_smul]
      exact congrArg (pointCosetEquiv x) (h p)
    · intro h p
      apply (pointCosetEquiv x).injective
      change pointCosetEquiv x ((p : G) • q) = pointCosetEquiv x q
      rw [pointCosetEquiv_smul]
      exact h p)

end CosetGeometry

section MovingCosets

variable {G : Type} [Group G] [Finite G] (H : Subgroup G) (P : Sylow 3 G)

def movingDoubleCosetEquiv :
    {q : DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G) //
      1 < (inducedOrbitStabilizer H (P : Subgroup G) q.out).index} ≃
        TernaryMovingOrbitCount.movingOrbits P (G ⧸ H) :=
  (inducedDoubleCosetOrbitEquiv H (P : Subgroup G)).subtypeEquiv (by
    intro q
    rw [inducedDoubleCosetOrbitEquiv_orbit, Nat.card_coe_set_eq,
      inducedOrbitStabilizer_index])

theorem movingDoubleCoset_card
    [Fintype (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G))] :
    (BinaryCoinducedSylowOrbitHead.movingOrbits H P).card =
      Nat.card (TernaryMovingOrbitCount.movingOrbits P (G ⧸ H)) := by
  calc
    _ = Nat.card {q : DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G) //
        1 < (inducedOrbitStabilizer H (P : Subgroup G) q.out).index} := by
      simp only [BinaryCoinducedSylowOrbitHead.movingOrbits,
        Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = _ := Nat.card_congr (movingDoubleCosetEquiv H P)

end MovingCosets

variable {X I C V : Type} [Finite X] [Finite I]
  {U : Subgroup (Equiv.Perm X)} [MulAction.IsPretransitive U X]
  [Group C] [Finite C] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (F : BinaryPairFrame U I) (hI : Nat.card I = 8) (x : X)
  (f : MulAction.stabilizer U x →* C) (hf : Function.Surjective f)
  (rho : Representation (ZMod 2) C V)
  (hC : Nat.card C = 3 ∨ Nat.card C = 6)
  (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)

include F hI in
theorem movingDoubleCosets_le_four (P : Sylow 3 U)
    [Fintype (DoubleCoset.Quotient
      ((MulAction.stabilizer U x) : Set U) ((P : Subgroup U) : Set U))] :
    (BinaryCoinducedSylowOrbitHead.movingOrbits (MulAction.stabilizer U x) P).card ≤ 4 := by
  have hX : Nat.card X = 16 := by
    rw [Nat.card_congr F.frame.symm, Nat.card_prod, hI, Nat.card_zmod]
  have hcoset : Nat.card (U ⧸ MulAction.stabilizer U x) = 16 :=
    (Nat.card_congr (pointCosetEquiv x)).trans hX
  have hfixed : 4 ≤ Nat.card
      (MulAction.fixedPoints P (U ⧸ MulAction.stabilizer U x)) := by
    rw [Nat.card_congr (fixedPointCosetEquiv x (P : Subgroup U))]
    exact BinaryPairTernaryFixedPoints.four_le_card_fixedPoints F
      (P : Subgroup U) P.isPGroup' hI
  rw [movingDoubleCoset_card]
  exact TernaryMovingOrbitCount.moving_le_four P
    (U ⧸ MulAction.stabilizer U x) P.isPGroup' hcoset hfixed

include F hI hf hC hdim hrho in
/-- Every actual correlated subrepresentation has head at most eight.
All local singleton-orbit fibres vanish by the actual Sylow image. -/
theorem original_head_le_eight
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer U x).subtype (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) U (ZMod 2))) ≤ 8 := by
  let P : Sylow 3 U := Classical.choice inferInstance
  letI : Finite (DoubleCoset.Quotient
      ((MulAction.stabilizer U x) : Set U) ((P : Subgroup U) : Set U)) :=
    Finite.of_injective
      (inducedDoubleCosetToOrbit (MulAction.stabilizer U x) (P : Subgroup U))
      (inducedDoubleCosetToOrbit_injective (MulAction.stabilizer U x) (P : Subgroup U))
  letI : Fintype (DoubleCoset.Quotient
      ((MulAction.stabilizer U x) : Set U) ((P : Subgroup U) : Set U)) :=
    Fintype.ofFinite _
  have h := BinaryCoinducedSylowOrbitHead.subrepresentation_head_le_twice_moving
    (MulAction.stabilizer U x) P f hf rho hC hdim hrho B
  have hm := movingDoubleCosets_le_four F hI x P
  omega

end SymmetricSubgroupAsymptotics.BinaryPairTernaryOrbitHead

end
