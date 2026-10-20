import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourNonbinaryFourPointCharts
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-! Transitivity and one genuine odd-order local element suffice for
primitivity on a four-point physical fibre. No new classification input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem nonbinary_fourPoint_preprimitive
    (T : Subgroup (Equiv.Perm (Fin 4)))
    [MulAction.IsPretransitive T (Fin 4)] (hnon : ¬ IsPGroup 2 T) :
    MulAction.IsPreprimitive T (Fin 4) := by
  rcases nonbinary_fourPoint_eq_alternating_or_top T hnon with hA | hS
  · subst T
    exact alternatingGroup.isPreprimitive_of_three_le_card (Fin 4) (by simp)
  · subst T
    let f : MulActionHom (fun g : Equiv.Perm (Fin 4) =>
        (⟨g,Subgroup.mem_top g⟩ : (⊤ : Subgroup (Equiv.Perm (Fin 4)))))
        (Fin 4) (Fin 4) := {
      toFun := id
      map_smul' := fun _ _ => rfl }
    exact MulAction.IsPreprimitive.of_surjective (f := f) Function.surjective_id

/-- Transport the four-point result on precisely the original fibre. -/
theorem nonbinary_card_four_preprimitive
    {F : Type} [Finite F] (T : Subgroup (Equiv.Perm F))
    [MulAction.IsPretransitive T F] (hF : Nat.card F = 4)
    (hnon : ¬ IsPGroup 2 T) : MulAction.IsPreprimitive T F := by
  let points : F ≃ Fin 4 := Finite.equivFinOfCardEq hF
  let S := relabelSubgroup points T
  let eG : T ≃* S := points.permCongrHom.subgroupMap T
  let f : MulActionHom eG F (Fin 4) := {
    toFun := points
    map_smul' := by
      intro s x
      change points (s.1 x) = ((points.permCongrHom.subgroupMap T s).1) (points x)
      simp [Equiv.permCongr_apply] }
  letI : MulAction.IsPretransitive S (Fin 4) :=
    MulAction.IsPretransitive.of_surjective_map (f := f) points.surjective inferInstance
  have hS : ¬ IsPGroup 2 S := by
    intro hp
    exact hnon (hp.of_injective eG.toMonoidHom eG.injective)
  letI : MulAction.IsPreprimitive S (Fin 4) := nonbinary_fourPoint_preprimitive S hS
  exact (MulAction.isPreprimitive_congr (f := f) eG.surjective points.bijective).mpr
    inferInstance

end SymmetricSubgroupAsymptotics
end
