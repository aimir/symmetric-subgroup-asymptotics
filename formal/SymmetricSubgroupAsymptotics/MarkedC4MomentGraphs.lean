import SymmetricSubgroupAsymptotics.Non2PreE7F20MarkedC4Numerics
import SymmetricSubgroupAsymptotics.JointSourceGraphs

/-!
# Exact graph model of the global marked `C4` moment

The summand `|Hom(J,C4)|^r` counts literal `r`-tuples of characters on one
source subgroup.  Their simultaneous graphs form distinct subgroups of
`C4^r × S_b`.  This file records the exact sigma-cardinality identity and
the resulting graph injection into the abstract subgroup lattice used by the
bounded-word RDT argument.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

abbrev MarkedC4JointSourceMaps (b r : ℕ) :=
  JointSourceMaps (Equiv.Perm (Fin b)) (Multiplicative (ZMod 4)) r

theorem markedC4JointSourceMaps_card (b r : ℕ) :
    Nat.card (MarkedC4JointSourceMaps b r) =
      ∑ J : Subgroup (Equiv.Perm (Fin b)),
        Nat.card (J →* Multiplicative (ZMod 4)) ^ r := by
  letI : Fintype (Subgroup (Equiv.Perm (Fin b))) := Fintype.ofFinite _
  letI (J : Subgroup (Equiv.Perm (Fin b))) : Finite
      (J →* Multiplicative (ZMod 4)) :=
    Finite.of_injective (fun f : J →* Multiplicative (ZMod 4) =>
      (f : J → Multiplicative (ZMod 4))) DFunLike.coe_injective
  rw [MarkedC4JointSourceMaps, JointSourceMaps, Nat.card_sigma]
  simp only [Nat.card_fun, Nat.card_fin]

/-- The real moment is the cast of the exact joint graph parameter count. -/
theorem markedC4Moment_eq_card_jointSourceMaps (b r : ℕ) :
    markedC4Moment b r = Nat.card (MarkedC4JointSourceMaps b r) := by
  unfold markedC4Moment
  rw [markedC4JointSourceMaps_card]
  norm_cast

/-- Simultaneous marked graphs in the abstract product.  Unlike the regular
permutation realization, this retains the auxiliary group as `C4^r` and
therefore does not charge four physical points per mark. -/
def markedC4AbstractGraph (b r : ℕ) :
    MarkedC4JointSourceMaps b r →
      Subgroup ((Fin r → Multiplicative (ZMod 4)) × Equiv.Perm (Fin b)) :=
  jointSourceGraph (G := Equiv.Perm (Fin b))
    (MonoidHom.id (Multiplicative (ZMod 4)))

theorem markedC4AbstractGraph_injective (b r : ℕ) :
    Function.Injective (markedC4AbstractGraph b r) :=
  jointSourceGraph_injective
    (G := Equiv.Perm (Fin b))
    (MonoidHom.id (Multiplicative (ZMod 4)))
    Function.surjective_id r

/-- Exact graph reduction of the marked moment to the subgroup count in
`C4^r × S_b`. -/
theorem markedC4Moment_le_abstractProductSubgroups (b r : ℕ) :
    markedC4Moment b r ≤
      Nat.card (Subgroup
        ((Fin r → Multiplicative (ZMod 4)) × Equiv.Perm (Fin b))) := by
  rw [markedC4Moment_eq_card_jointSourceMaps]
  exact_mod_cast Nat.card_le_card_of_injective
    (markedC4AbstractGraph b r) (markedC4AbstractGraph_injective b r)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
