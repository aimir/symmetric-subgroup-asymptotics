import SymmetricSubgroupAsymptotics.BinaryCarrierAlphabetWordClosure
import SymmetricSubgroupAsymptotics.BinaryActionCoverage8

/-!
# The eight base degree-eight actions in the carrier alphabet

Seven base entries are the literal degree-eight original-action colours.
The remaining entry is the critical `E8` action.  This file gives the exact
point relabelling for all eight registry entries, so the base branch of the
degree-eight physical classifier can be used as unchanged carrier-alphabet
slots.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryDegreeEightBaseRoutes

open SymmetricSubgroupAsymptotics
open BinaryCarrierProfileTransport
open BinaryActionRegistry8

local instance : Inhabited (criticalActionPoints .e8) := ⟨(0,0)⟩

/-- The eight action-registry entries omitted from the nonbase normal
registry. -/
inductive Base
  | t18 | e8 | t26 | t27 | t28 | t29 | t31 | t35
  deriving DecidableEq, Fintype

def baseIndex : Base → Fin 26
  | .t18 => 14
  | .e8 => 18
  | .t26 => 19
  | .t27 => 20
  | .t28 => 21
  | .t29 => 22
  | .t31 => 24
  | .t35 => 25

/-- Their exact colours in the completed mixture alphabet. -/
def baseKind : Base → MixtureKind
  | .t18 => .inr (some (.degree8 .t18))
  | .e8 => .inl .e8
  | .t26 => .inr (some (.degree8 .t26))
  | .t27 => .inr (some (.degree8 .t27))
  | .t28 => .inr (some (.degree8 .t28))
  | .t29 => .inr (some (.degree8 .t29))
  | .t31 => .inr (some (.degree8 .t31))
  | .t35 => .inr (some (.degree8 .t35))

private def e8NaturalIndex (x : criticalActionPoints .e8) : Fin 8 :=
  ⟨(x.1 0).val + 2 * (x.1 1).val + 4 * x.2.val,by
    have h0 := (x.1 0).val_lt
    have h1 := (x.1 1).val_lt
    have h2 := x.2.val_lt
    omega⟩

/-- Explicit binary-coordinate numbering of the critical `E8` points. -/
def e8PointEquiv : criticalActionPoints .e8 ≃ Fin 8 where
  toFun x :=
    (#[0,1,3,5,7,2,4,6] : Array (Fin 8))[(e8NaturalIndex x).val]!
  invFun i :=
    (#[(
        ![0,0],0),
      (![1,0],0),
      (![1,0],1),
      (![0,1],0),
      (![0,1],1),
      (![1,1],0),
      (![1,1],1),
      (![0,0],1)] : Array (criticalActionPoints .e8))[i.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Exact point relabelling from every base mixture colour to its registry
action. -/
def basePointEquiv : (i : Base) → mixturePoints (baseKind i) ≃ Fin 8
  | .t18 => Equiv.refl _
  | .e8 => e8PointEquiv
  | .t26 => Equiv.refl _
  | .t27 => Equiv.refl _
  | .t28 => Equiv.refl _
  | .t29 => Equiv.refl _
  | .t31 => Equiv.refl _
  | .t35 => Equiv.refl _

private def e8GeneratorLift : Fin 5 → BinaryHeisenberg 2
  | 0 => ⟨![0,0],![0,0],1⟩
  | 1 => ⟨![1,0],![0,1],1⟩
  | 2 => ⟨![0,1],![1,0],1⟩
  | 3 => ⟨![0,0],![1,1],0⟩
  | 4 => ⟨![0,0],![1,0],0⟩

private theorem e8_generator_image (j : Fin 5) :
    e8PointEquiv.permCongr (BinaryHeisenberg.action 2 (e8GeneratorLift j)) =
      BinaryMenuCayley8T22.generators j := by
  apply Equiv.ext
  intro x
  revert x j
  decide +kernel

private theorem e8_action_eq_t22 :
    relabelSubgroup e8PointEquiv (criticalActionSubgroup .e8) =
      Subgroup.closure (Set.range BinaryMenuCayley8T22.generators) := by
  apply (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    change BinaryMenuCayley8T22.generators j ∈
      (criticalActionSubgroup .e8).map e8PointEquiv.permCongrHom.toMonoidHom
    rw [← e8_generator_image j]
    exact ⟨BinaryHeisenberg.action 2 (e8GeneratorLift j),
      ⟨e8GeneratorLift j,rfl⟩,rfl⟩
  · have hleft : Nat.card
        (relabelSubgroup e8PointEquiv (criticalActionSubgroup .e8)) = 32 := by
      let E := (criticalActionSubgroup .e8).equivMapOfInjective
        e8PointEquiv.permCongrHom.toMonoidHom
          e8PointEquiv.permCongrHom.injective
      change Nat.card ((criticalActionSubgroup .e8).map
        e8PointEquiv.permCongrHom.toMonoidHom) = 32
      rw [← Nat.card_congr E.toEquiv,criticalAction_group_card]
      rfl
    rw [hleft,BinaryMenuCayley8T22.exact_card]

/-- Every omitted base registry action is exactly an unchanged colour in the
completed mixture alphabet. -/
theorem base_action_eq (i : Base) :
    relabelSubgroup (basePointEquiv i) (mixtureAction (baseKind i)) =
      actions (baseIndex i) := by
  cases i with
  | t18 =>
      change relabelSubgroup (Equiv.refl (Fin 8))
        (Subgroup.closure (Set.range BinaryMenuCayley8T18.generators)) = _
      exact relabelSubgroup_refl _
  | e8 =>
      change relabelSubgroup e8PointEquiv (criticalActionSubgroup .e8) = _
      exact e8_action_eq_t22
  | t26 =>
      change relabelSubgroup (Equiv.refl (Fin 8))
        (Subgroup.closure (Set.range BinaryMenuCayley8T26.generators)) = _
      exact relabelSubgroup_refl _
  | t27 =>
      change relabelSubgroup (Equiv.refl (Fin 8))
        (Subgroup.closure (Set.range BinaryMenuCayley8T27.generators)) = _
      exact relabelSubgroup_refl _
  | t28 =>
      change relabelSubgroup (Equiv.refl (Fin 8))
        (Subgroup.closure (Set.range BinaryMenuCayley8T28.generators)) = _
      exact relabelSubgroup_refl _
  | t29 =>
      change relabelSubgroup (Equiv.refl (Fin 8))
        (Subgroup.closure (Set.range BinaryMenuCayley8T29.generators)) = _
      exact relabelSubgroup_refl _
  | t31 =>
      change relabelSubgroup (Equiv.refl (Fin 8))
        (Subgroup.closure (Set.range BinaryMenuCayley8T31.generators)) = _
      exact relabelSubgroup_refl _
  | t35 =>
      change relabelSubgroup (Equiv.refl (Fin 8))
        (Subgroup.closure (Set.range BinaryMenuCayley8T35.generators)) = _
      exact relabelSubgroup_refl _

end SymmetricSubgroupAsymptotics.BinaryDegreeEightBaseRoutes
