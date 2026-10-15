import SymmetricSubgroupAsymptotics.BinaryPairTernaryOrbitHead
import SymmetricSubgroupAsymptotics.TernaryLargeOrbitMovingCount

/-! An actual nine-point Sylow-three orbit on sixteen original cosets
forces the coinduced binary head to be at most six. The inducing subgroup,
local epimorphism and faithful two-dimensional representation remain exact. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCoinducedLargeOrbitHead

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable {G L V : Type} [Group G] [Finite G] [Group L] [Finite L]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (H : Subgroup G) (P : Sylow 3 G)
    (f : H →* L) (hf : Function.Surjective f)
    (rho : Representation (ZMod 2) L V)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)

include hf hL hdim hrho in
/-- The six-dimensional bound follows from actual orbit geometry, not
from an assumed representation capacity or a list of submodules. -/
theorem head_le_six
    (hindex : Nat.card (G ⧸ H) = 16) (y : G ⧸ H)
    (hy : 9 ≤ Nat.card (MulAction.orbit P y))
    (B : Subrepresentation (Representation.coind H.subtype (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2))) ≤ 6 := by
  letI : Finite (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) :=
    Finite.of_injective (inducedDoubleCosetToOrbit H (P : Subgroup G))
      (inducedDoubleCosetToOrbit_injective H (P : Subgroup G))
  letI : Fintype (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) :=
    Fintype.ofFinite _
  have h := BinaryCoinducedSylowOrbitHead.subrepresentation_head_le_twice_moving
    H P f hf rho hL hdim hrho B
  have hcount := TernaryMovingOrbitCount.moving_le_three_of_large_orbit
    P (G ⧸ H) P.isPGroup' hindex y hy
  rw [BinaryPairTernaryOrbitHead.movingDoubleCoset_card H P] at h
  omega

include hf hL hdim hrho in
/-- An actual equivariant block map on the original cosets provides the
large orbit from the original block and kernel orbits. -/
theorem head_le_six_of_block_and_fibre
    {I : Type} [Finite I] [MulAction P I]
    (b : (G ⧸ H) → I)
    (hb : ∀ (g : P) (z : G ⧸ H), b (g • z) = g • b z)
    (K : Subgroup P) (hindex : Nat.card (G ⧸ H) = 16)
    (y : G ⧸ H) (hK : ∀ k : K, (k : P) • b y = b y)
    (hblock : 3 ≤ Nat.card (MulAction.orbit P (b y)))
    (hfibre : 3 ≤ Nat.card (MulAction.orbit K y))
    (B : Subrepresentation (Representation.coind H.subtype (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2))) ≤ 6 :=
  head_le_six H P f hf rho hL hdim hrho hindex y
    ((Nat.mul_le_mul hblock hfibre).trans
      (orbit_card_ge_block_mul_fibre b hb K y hK)) B

end SymmetricSubgroupAsymptotics.BinaryCoinducedLargeOrbitHead

end
