import SymmetricSubgroupAsymptotics.CFSGSufficientSimpleIndexBounds
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawChart
import SymmetricSubgroupAsymptotics.CFSGOuterCardinalityCancellation

/-! The automorphism-square estimate needed by the actual semisimple
coefficients follows from the sufficient simple-index bounds. This avoids
requiring a generating pair for each simple group in those consumers.
Both the inner automorphism subgroup and its literal quotient are counted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open PrimitiveSocleRawStructure

def FiniteSimpleAutomorphismSquareBound : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsCenterless G →
    Nat.card (MulAut G) ≤ Nat.card G ^ 2

theorem finiteSimpleAutomorphismSquareBound_of_sufficient
    (hindex : SufficientSimpleIndexBounds) : FiniteSimpleAutomorphismSquareBound := by
  intro G _ _ hs hc
  letI : IsSimpleGroup G := hs
  have hn : ¬IsMulCommutative G := by
    intro hcomm
    obtain ⟨g,hg⟩ := exists_ne (1 : G)
    exact hg (hc g (fun h => (isMulCommutative_iff.mp hcomm) g h))
  obtain ⟨ell,hell⟩ := exists_leastProperIndex G
  obtain ⟨horder,hbudget⟩ := hindex G hn ell hell
  have hf : 5 ≤ ell := nonabelianSimple_leastProperIndex_five_le
    (fun h => hn (isMulCommutative_iff.mpr h)) hell.1
  have hfour := hbudget.square_bound hf
  have hout : Nat.card (Outer G) ≤ Nat.card G := by omega
  have hinner : Nat.card (PrimitiveSocleRawStructure.Inner G) = Nat.card G :=
    (Nat.card_congr (MonoidHom.ofInjective
      (CFSGOuterCardinalityCancellation.conj_injective hn)).toEquiv).symm
  have hcard := (PrimitiveSocleRawStructure.Inner G).card_mul_index
  change Nat.card (PrimitiveSocleRawStructure.Inner G) * Nat.card (Outer G) =
    Nat.card (MulAut G) at hcard
  rw [hinner] at hcard
  calc
    Nat.card (MulAut G) = Nat.card G * Nat.card (Outer G) := hcard.symm
    _ ≤ Nat.card G * Nat.card G := Nat.mul_le_mul_left _ hout
    _ = Nat.card G ^ 2 := (pow_two _).symm

end SymmetricSubgroupAsymptotics
