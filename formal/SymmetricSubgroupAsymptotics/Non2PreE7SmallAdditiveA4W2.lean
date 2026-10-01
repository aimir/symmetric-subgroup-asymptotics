import SymmetricSubgroupAsymptotics.Non2PreE7A4WreathC2Group
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelRelabel

/-!
# A4W2: natural `A₄ ≀ C₂` on eight points (D0386)

The family is exactly the natural imprimitive action of `A₄ ≀ C₂` on two
blocks of four points, up to relabeling.  Every nontrivial normal subgroup
contains the base `V₄ × V₄`, the kernel of the action on the six block
pairings, so the literal nontrivial quotients are quotients of the pairing
image `C₃ ≀ C₂` in its faithful degree-six action.  The onto maps to
`A₄ ≀ C₂` use the common source `J''`:

`Z_J(A₄ ≀ C₂) ≤ Z_J(C₃ ≀ C₂) + |Aut| · 2^(b/2)`.

At `w = 8` the comparator degree `6` and the slope `1/2` meet the
`ρ = 1/8192` window.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

open Equiv A4WreathC2

/-- The A4W2 family: the natural action of `A₄ ≀ C₂` on two blocks of four.
The relabelling is retained as data because the numerical owner must reuse
the same literal model. -/
structure PreE7A4W2Source (w : ℕ) (i : PreE7NonPairActionClass w) : Type where
  chart : Fin 4 ⊕ Fin 4 ≃ Fin w
  action_eq : preE7NonPairAction w i =
    relabelSubgroup chart A4WreathC2.natural.range

/-- The comparator model of natural `A₄ ≀ C₂`. -/
def a4w2Model {w : ℕ} (i : PreE7NonPairActionClass w) (e : Fin 4 ⊕ Fin 4 ≃ Fin w)
    (h : preE7NonPairAction w i = relabelSubgroup e A4WreathC2.natural.range) :
    PreE7NormalComparatorModel w i where
  G := A4WreathC2.G
  equiv := relabelModelEquiv A4WreathC2.natural natural_injective e h
  index := Unit
  R := blockPairing.range
  degree := 3 + 3
  action := ((finSumFinEquiv (m := 3) (n := 3)).permCongrHom.toMonoidHom).comp
    blockPairing.range.subtype
  action_injective := by
    intro x y hxy
    exact Subtype.val_injective ((finSumFinEquiv (m := 3) (n := 3)).permCongrHom.injective hxy)
  proj := fun _ => blockPairing.rangeRestrict
  proj_surjective := fun _ => blockPairing.rangeRestrict_surjective
  normal_cover := fun N hN hNb => by
    haveI := hN
    refine ⟨(), ?_⟩
    rw [MonoidHom.ker_rangeRestrict]
    exact le_of_minimal_selfCentralizing V V_minimal V_selfCentralizing N hNb
  tailSlope := 1 / 2
  tailConstant := Nat.card (A4WreathC2.G ≃* A4WreathC2.G)
  tailConstant_nonneg := by positivity
  tail := fun _ J => A4WreathC2.epi_card_le J
  comparator_window := by
    have hw : w = 8 := by
      rw [width_eq_of_relabel e]
      simp
    subst hw
    norm_num [preE7CharacterRho, evenWidth, halfDegree]
  tail_window := by
    have hw : w = 8 := by
      rw [width_eq_of_relabel e]
      simp
    subst hw
    norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree]

/-- **A4W2.**  Every natural `A₄ ≀ C₂` action is accepted by the mixed local
catalogue. -/
theorem preE7_a4w2_localFamilyAction (w : ℕ) (i : PreE7NonPairActionClass w)
    (S : PreE7A4W2Source w i) : preE7NoPairNoC3EarlierLocalFamilyAction .a4w2 w i := by
  exact (a4w2Model i S.chart S.action_eq).localFamilyAction .a4w2

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
