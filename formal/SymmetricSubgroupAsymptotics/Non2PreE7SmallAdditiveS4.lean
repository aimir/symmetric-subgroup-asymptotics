import SymmetricSubgroupAsymptotics.Non2PreE7NaturalS4Group

/-!
# S4: the natural degree-four symmetric group (D0384)

The family is exactly an actual natural degree-four `S₄` orbit: width four and
the whole symmetric group.  Its literal normal menu is `1, V₄, A₄, S₄`; every
nontrivial kernel contains `V₄ = ker(S₄ → S₃)`, so those quotients are literal
quotients of the natural `S₃` comparator on three points.  The onto maps to
`S₄` use the common second derived source `J''` and the common-head count:

`Z_J(S₄) ≤ Z_J(S₃) + 2 |Aut S₄| · 2^(b/4)`.

At `w = 4` the comparator degree `3` and the slope `1/4` meet the
`ρ = 1/8192` window.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

open Equiv

/-- The S4 family: the full symmetric group in its natural degree-four action. -/
structure PreE7S4Source (w : ℕ) (i : PreE7NonPairActionClass w) : Prop where
  degree : w = 4
  full : preE7NonPairAction w i = ⊤

/-- The comparator model of natural `S₄`. -/
def s4Model (i : PreE7NonPairActionClass 4) (h : preE7NonPairAction 4 i = ⊤) :
    PreE7NormalComparatorModel 4 i where
  G := Perm (Fin 4)
  equiv := (MulEquiv.subgroupCongr h).trans Subgroup.topEquiv
  index := Unit
  R := Perm (Fin 3)
  degree := 3
  action := MonoidHom.id _
  action_injective := Function.injective_id
  proj := fun _ => NaturalS4.pairing
  proj_surjective := fun _ => NaturalS4.pairing_surjective
  normal_cover := fun N hN hNb => by
    haveI := hN
    refine ⟨(), ?_⟩
    rw [NaturalS4.ker_pairing]
    exact le_of_minimal_selfCentralizing NaturalS4.klein NaturalS4.klein_minimal
      NaturalS4.klein_selfCentralizing N hNb
  tailSlope := 1 / 4
  tailConstant := 2 * Nat.card (Perm (Fin 4) ≃* Perm (Fin 4))
  tailConstant_nonneg := by positivity
  tail := fun _ J => NaturalS4.epi_card_le J
  comparator_window := by
    norm_num [preE7CharacterRho, evenWidth, halfDegree]
  tail_window := by
    norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree]

/-- **S4.**  Every natural `S₄` action is accepted by the mixed local
catalogue. -/
theorem preE7_s4_localFamilyAction (w : ℕ) (i : PreE7NonPairActionClass w)
    (S : PreE7S4Source w i) : preE7NoPairNoC3EarlierLocalFamilyAction .s4 w i := by
  obtain ⟨rfl, h⟩ := S
  exact (s4Model i h).localFamilyAction .s4

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
