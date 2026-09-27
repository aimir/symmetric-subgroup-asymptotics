import SymmetricSubgroupAsymptotics.DegreeThreeBlockInversionHead
import SymmetricSubgroupAsymptotics.OriginalMinimalBlock

/-!
# The degree-twenty-seven minimal-block owner

This file installs the degree-three block-kernel dichotomy on the literal
minimal block selected from an original transitive action.  A chart of the
base fibre is transported by the original action to every other fibre; no
independent product of symmetric groups is introduced.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω]
variable [MulAction.IsPretransitive A Ω]
variable {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

/-- A three-point chart on the base fibre, transported to every literal
fibre by an element of the original transitive action on the block set. -/
def ternaryFibreCharts [Finite A] [Finite Ω]
    (hFibre : Nat.card D.Fibre = 3) :
    ∀ x : D.Points, Fin 3 ≃ originalBlockFibre D.map x := by
  intro x
  let e₀ : Fin 3 ≃ D.Fibre :=
    (Finite.equivFinOfCardEq hFibre).symm
  let a : A := Classical.choose (MulAction.exists_smul_eq A D.base x)
  have ha : a • D.base = x :=
    Classical.choose_spec (MulAction.exists_smul_eq A D.base x)
  simpa only [ha] using
    e₀.trans
      (OriginalBlockSignCoordinates.fibreTransport
        D.map D.map_equivariant a D.base)

/-- The complete checked inversion dichotomy, specialized to the actual
minimal block of an original action. -/
theorem degreeTwentySeven_closure
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    (N : Subgroup A) [N.Normal]
    (hDegree : Nat.card Ω = 27)
    (hFibre : Nat.card D.Fibre = 3)
    (hTopGroup : IsPGroup 3 D.Top)
    (hTop : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) ≤ 2) :
    (20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) <
        3 * Nat.card Ω) ∨ IsPGroup 3 A := by
  letI : Fintype D.Points := Fintype.ofFinite _
  letI (x : D.Points) : Fintype (originalBlockFibre D.map x) :=
    Fintype.ofFinite _
  have h := DegreeThreeBlockInversionHead.originalNormal_degreeTwentySeven_closure
    D.map D.map_equivariant N (D.ternaryFibreCharts hFibre) hTopGroup hTop
  simpa only [hDegree] using h

/-- A pair strictly above the `3/20` line cannot take the numerical side of
the degree-twenty-seven dichotomy and therefore enters the existing ternary
group owner. -/
theorem degreeTwentySeven_high_isPGroup
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    (N : Subgroup A) [N.Normal]
    (hDegree : Nat.card Ω = 27)
    (hFibre : Nat.card D.Fibre = 3)
    (hTopGroup : IsPGroup 3 D.Top)
    (hTop : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) ≤ 2)
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    IsPGroup 3 A := by
  rcases D.degreeTwentySeven_closure N hDegree hFibre hTopGroup hTop with
    hSafe | hOwner
  · omega
  · exact hOwner

end OriginalMinimalBlock

end SymmetricSubgroupAsymptotics

end
