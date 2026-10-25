import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Prod

/-! An invariant additive central graph splits under an actual sign
flip. Only additive subgroup structure is used; no larger-field
linearity of the subgroup is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AdditiveCentralGraphFlip
variable {V Z : Type*} [AddCommGroup V] [AddCommGroup Z]

theorem snd_eq_zero_of_flip (C : AddSubgroup (V × Z))
    (htwo : ∀ z : Z, z+z=0 → z=0)
    (hvertical : ∀ z : Z, (0,z) ∈ C → z=0)
    (hflip : ∀ x ∈ C, (-x.1,x.2) ∈ C) :
    ∀ x ∈ C, x.2=0 := by
  intro x hx
  have hs := C.add_mem hx (hflip x hx)
  have he : x+(-x.1,x.2) = (0,x.2+x.2) := by
    apply Prod.ext <;> simp
  rw [he] at hs
  exact htwo x.2 (hvertical (x.2+x.2) hs)

theorem eq_horizontal_of_flip_card [Finite V]
    (C : AddSubgroup (V × Z))
    (htwo : ∀ z : Z, z+z=0 → z=0)
    (hvertical : ∀ z : Z, (0,z) ∈ C → z=0)
    (hflip : ∀ x ∈ C, (-x.1,x.2) ∈ C)
    (hcard : Nat.card C = Nat.card V) :
    C = (AddMonoidHom.snd V Z).ker := by
  have hle : C ≤ (AddMonoidHom.snd V Z).ker := snd_eq_zero_of_flip C htwo hvertical hflip
  let e : (AddMonoidHom.snd V Z).ker ≃ V :=
    { toFun := fun x => x.val.1
      invFun := fun v => ⟨(v,0),rfl⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact Prod.ext rfl x.property.symm
      right_inv := fun _ => rfl }
  letI : Finite (AddMonoidHom.snd V Z).ker := Finite.of_equiv V e.symm
  have hk : Nat.card (AddMonoidHom.snd V Z).ker = Nat.card V := Nat.card_congr e
  exact AddSubgroup.eq_of_le_of_card_ge hle (by rw [hk,hcard])

end SymmetricSubgroupAsymptotics.AdditiveCentralGraphFlip
