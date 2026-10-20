import SymmetricSubgroupAsymptotics.BinaryThreeQuartetCubicImageSocles

/-! Faithfulness of the literal two-binary-regular C3 affine action.
Only coordinate evaluations are used, with no model-group enumeration. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryThreeQuartetCubicImageSocles

@[simp] theorem regular_pointAction_apply (g : Model) (p : Plane × CyclicThree) :
    pointAction g p =
      ((fun i => g.left.toAdd (i,g.right*p.2) + p.1 i),g.right*p.2) := rfl

theorem regular_pointAction_injective : Function.Injective pointAction := by
  intro g h he
  have hr : g.right = h.right := by
    have hv := congrArg (fun f : Equiv.Perm (Plane × CyclicThree) => (f (0,1)).2) he
    simpa only [regular_pointAction_apply,mul_one] using hv
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext x
    rcases x with ⟨i,c⟩
    have hv := congrArg (fun f : Equiv.Perm (Plane × CyclicThree) =>
      (f (0,g.right⁻¹*c)).1 i) he
    simpa only [regular_pointAction_apply,Pi.zero_apply,add_zero,hr,mul_inv_cancel_left] using hv
  · exact hr

theorem regular_literalAction_injective (e : Plane × CyclicThree ≃ Fin 12) :
    Function.Injective (literalAction e) := by
  intro g h he
  apply regular_pointAction_injective
  apply e.permCongrHom.injective
  exact he

end SymmetricSubgroupAsymptotics.BinaryThreeQuartetCubicImageSocles
end
