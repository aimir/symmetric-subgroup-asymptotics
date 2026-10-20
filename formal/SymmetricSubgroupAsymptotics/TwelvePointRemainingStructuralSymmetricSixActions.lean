import SymmetricSubgroupAsymptotics.SymmetricFourTwelvePointSocles

/-! Both transitive six-point S4 actions used by the remaining literal
pair tops. The second action twists the edge action by complementary edges
on odd permutations. No source group identification is inferred from order. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSymmetricSixActions
open SymmetricFourTwelvePointSocles (edge)

def opposite : Equiv.Perm (Fin 6) where
  toFun := ![5,4,3,2,1,0]
  invFun := ![5,4,3,2,1,0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem opposite_square : opposite*opposite=1 := by decide +kernel

theorem opposite_edge_commute (g : Equiv.Perm (Fin 4)) : Commute opposite (edge g) := by
  apply Equiv.ext
  intro i
  revert g i
  decide +kernel

def signComplement : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 6) where
  toFun g := if Equiv.Perm.sign g=1 then 1 else opposite
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul]
    rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hg | hg <;>
      rcases Int.units_eq_one_or (Equiv.Perm.sign h) with hh | hh <;>
      simp [hg,hh,opposite_square]

theorem signComplement_edge_commute (g h : Equiv.Perm (Fin 4)) :
    Commute (signComplement g) (edge h) := by
  change Commute (if Equiv.Perm.sign g=1 then 1 else opposite) (edge h)
  split
  · exact Commute.one_left _
  · exact opposite_edge_commute h

def twistedEdge : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 6) where
  toFun g := edge g * signComplement g
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul,map_mul]
    have hc := (signComplement_edge_commute g h).eq.symm
    calc
      (edge g * edge h) * (signComplement g * signComplement h) =
          edge g * (edge h * signComplement g) * signComplement h := by group
      _ = edge g * (signComplement g * edge h) * signComplement h := by rw [hc]
      _ = (edge g * signComplement g) * (edge h * signComplement h) := by group

theorem edge_injective : Function.Injective edge := by
  intro g h he
  have detect : ∀ g h : Equiv.Perm (Fin 4),
    (∀ i : Fin 6, edge g i=edge h i) → ∀ j : Fin 4, g j=h j := by decide +kernel
  exact Equiv.ext (detect g h (fun i => congrArg (fun a : Equiv.Perm (Fin 6) => a i) he))

theorem twistedEdge_injective : Function.Injective twistedEdge := by
  intro g h he
  have detect : ∀ g h : Equiv.Perm (Fin 4),
    (∀ i : Fin 6, twistedEdge g i=twistedEdge h i) → ∀ j : Fin 4, g j=h j := by decide +kernel
  exact Equiv.ext (detect g h (fun i => congrArg (fun a : Equiv.Perm (Fin 6) => a i) he))

end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSymmetricSixActions
