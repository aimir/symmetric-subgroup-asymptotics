import SymmetricSubgroupAsymptotics.PrimitiveCompositionLengthInput
import Mathlib.Algebra.Group.Subgroup.Map

/-!
# Relabelling the published primitive composition-length bound

The literature interface is stated on `Fin r`.  Actual minimal blocks live
on their literal fibres.  This file transports both the primitive action
and a literal subnormal composition series through the canonical finite
relabeling, preserving its length definitionally.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace SubnormalCompositionSeries

variable {G H : Type} [Group G] [Group H]

/-- A group equivalence transports the poset of subnormal subgroups. -/
def subnormalPointMapEquiv (e : G ≃* H) :
    SubnormalPoint G ≃o SubnormalPoint H where
  toFun K := ⟨e.mapSubgroup K.1, K.2.map e.surjective⟩
  invFun K := ⟨e.symm.mapSubgroup K.1, K.2.map e.symm.surjective⟩
  left_inv K := by
    apply Subtype.ext
    exact e.mapSubgroup.left_inv K.1
  right_inv K := by
    apply Subtype.ext
    exact e.mapSubgroup.right_inv K.1
  map_rel_iff' := by
    intro K L
    exact e.mapSubgroup.le_iff_le

/-- Transport an actual composition series through a group equivalence. -/
def mapEquiv (e : G ≃* H) (t : SubnormalCompositionSeries G) :
    SubnormalCompositionSeries H where
  chain :=
    { length := t.chain.length
      toFun := fun i ↦ subnormalPointMapEquiv e (t.chain i)
      step := fun i ↦ by
        exact (apply_covBy_apply_iff
          (subnormalPointMapEquiv e)).2 (t.chain.step i) }
  head := by
    change e.mapSubgroup t.chain.head.1 = ⊥
    rw [t.head]
    exact e.mapSubgroup.map_bot
  last := by
    change e.mapSubgroup t.chain.last.1 = ⊤
    rw [t.last]
    exact e.mapSubgroup.map_top

@[simp] theorem mapEquiv_length (e : G ≃* H)
    (t : SubnormalCompositionSeries G) :
    (mapEquiv e t).chain.length = t.chain.length := rfl

end SubnormalCompositionSeries

namespace PrimitiveCompositionLengthInput

variable {Ω : Type} [Fintype Ω]

/-- The literal permutation group after relabelling the acted-on finite type
by an equivalence with `Fin r`. -/
def relabelGroup (r : ℕ) (e : Ω ≃ Fin r)
    (U : Subgroup (Equiv.Perm Ω)) : Subgroup (Equiv.Perm (Fin r)) :=
  e.permCongrHom.mapSubgroup U

/-- Relabelling gives the corresponding group equivalence. -/
def relabelGroupEquiv (r : ℕ) (e : Ω ≃ Fin r)
    (U : Subgroup (Equiv.Perm Ω)) :
    U ≃* relabelGroup r e U :=
  e.permCongrHom.subgroupMap U

/-- The published primitive composition-length theorem applies to a
literal finite action after relabelling, with no change to the supplied
composition-series length. -/
theorem bound_of_equiv
    (hcomp : PrimitiveCompositionLengthInput)
    (r : ℕ) (hr : 2 ≤ r) (e : Ω ≃ Fin r)
    (U : Subgroup (Equiv.Perm Ω))
    (hprimitive : MulAction.IsPreprimitive U Ω)
    (t : SubnormalCompositionSeries U) :
    (t.chain.length : ℝ) ≤
      (8 / 3 : ℝ) * Real.logb 2 r - 4 / 3 := by
  let V := relabelGroup r e U
  let g : U ≃* V := relabelGroupEquiv r e U
  let f : Ω →ₑ[g] Fin r :=
    { toFun := e
      map_smul' := by
        intro u x
        change e (u.1 x) = e (u.1 (e.symm (e x)))
        rw [e.symm_apply_apply] }
  have hV : MulAction.IsPreprimitive V (Fin r) :=
    (MulAction.isPreprimitive_congr g.surjective
      (show Function.Bijective f from e.bijective)).mp hprimitive
  let tV : SubnormalCompositionSeries V := t.mapEquiv g
  simpa only [tV, SubnormalCompositionSeries.mapEquiv_length] using
    hcomp r hr V hV tV

end PrimitiveCompositionLengthInput
end SymmetricSubgroupAsymptotics

end
