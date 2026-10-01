import Mathlib.GroupTheory.RegularWreathProduct

/-!
# The faithful permutational wreath action

The regular wreath product in Mathlib uses the regular action of its top
group.  Block compression instead retains an arbitrary faithful action of
the actual top.  This file constructs the corresponding permutational wreath
product and its faithful action on the product of the base and top point
sets.  In finite degrees `u` and `s`, the action is then relabelled on
`Fin (u * s)`.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- The permutational wreath product attached to a `Q`-set `I`. -/
@[ext]
structure PermutationalWreathProduct
    (D Q I : Type*) [Group D] [Group Q] [MulAction Q I] where
  left : I → D
  right : Q

namespace PermutationalWreathProduct

variable {D Q I : Type*} [Group D] [Group Q] [MulAction Q I]

instance : Mul (PermutationalWreathProduct D Q I) where
  mul a b :=
    ⟨a.left * (fun x ↦ b.left (a.right⁻¹ • x)), a.right * b.right⟩

@[simp] theorem mul_left (a b : PermutationalWreathProduct D Q I) :
    (a * b).left = a.left * (fun x ↦ b.left (a.right⁻¹ • x)) := rfl

@[simp] theorem mul_right (a b : PermutationalWreathProduct D Q I) :
    (a * b).right = a.right * b.right := rfl

instance : One (PermutationalWreathProduct D Q I) where
  one := ⟨1, 1⟩

@[simp] theorem one_left :
    (1 : PermutationalWreathProduct D Q I).left = 1 := rfl

@[simp] theorem one_right :
    (1 : PermutationalWreathProduct D Q I).right = 1 := rfl

instance : Inv (PermutationalWreathProduct D Q I) where
  inv x := ⟨fun k ↦ x.left⁻¹ (x.right • k), x.right⁻¹⟩

@[simp] theorem inv_left (a : PermutationalWreathProduct D Q I) :
    a⁻¹.left = fun x ↦ a.left⁻¹ (a.right • x) := rfl

@[simp] theorem inv_right (a : PermutationalWreathProduct D Q I) :
    a⁻¹.right = a.right⁻¹ := rfl

instance : Group (PermutationalWreathProduct D Q I) where
  mul_assoc a b c := by ext <;> simp [mul_assoc, smul_smul]
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv_mul_cancel a := by ext <;> simp

instance : Inhabited (PermutationalWreathProduct D Q I) := ⟨1⟩

/-- Projection to the actual top group. -/
def rightHom : PermutationalWreathProduct D Q I →* Q where
  toFun := right
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The actual top embeds with trivial base coordinate. -/
def topHom : Q →* PermutationalWreathProduct D Q I where
  toFun q := ⟨1, q⟩
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

theorem topHom_injective :
    Function.Injective (topHom (D := D) (Q := Q) (I := I)) := by
  intro q q' h
  exact congrArg right h

section Action

variable {Lambda : Type*} [MulAction D Lambda]

instance : SMul (PermutationalWreathProduct D Q I) (Lambda × I) where
  smul w p := ⟨w.left (w.right • p.2) • p.1, w.right • p.2⟩

@[simp] theorem smul_def
    (w : PermutationalWreathProduct D Q I) (p : Lambda × I) :
    w • p = ⟨w.left (w.right • p.2) • p.1, w.right • p.2⟩ := rfl

instance : MulAction (PermutationalWreathProduct D Q I) (Lambda × I) where
  one_smul := by simp
  mul_smul := by simp [smul_smul]

instance [FaithfulSMul D Lambda] [FaithfulSMul Q I]
    [Nonempty Lambda] [Nonempty I] :
    FaithfulSMul (PermutationalWreathProduct D Q I) (Lambda × I) where
  eq_of_smul_eq_smul := by
    intro a b h
    let ⟨x₀⟩ := (inferInstance : Nonempty Lambda)
    have hright : a.right = b.right :=
      eq_of_smul_eq_smul (M := Q) (α := I)
        (fun i ↦ congrArg Prod.snd (h (x₀, i)))
    apply PermutationalWreathProduct.ext
    · funext i
      apply eq_of_smul_eq_smul (M := D) (α := Lambda)
      intro x
      have hx := congrArg Prod.fst (h (x, a.right⁻¹ • i))
      simpa only [smul_def, hright, smul_inv_smul] using hx
    · exact hright

/-- The faithful product-point action. -/
def toPerm :
    PermutationalWreathProduct D Q I →* Equiv.Perm (Lambda × I) :=
  MulAction.toPermHom _ _

theorem toPerm_injective [FaithfulSMul D Lambda] [FaithfulSMul Q I]
    [Nonempty Lambda] [Nonempty I] :
    Function.Injective (toPerm (D := D) (Q := Q) (I := I) (Lambda := Lambda)) :=
  MulAction.toPerm_injective

end Action

section FiniteDegree

variable {u s : ℕ}
  (D Q : Type*) [Group D] [Group Q]
  [MulAction D (Fin u)] [MulAction Q (Fin s)]

/-- Relabel the product-point wreath action on exactly `u * s` points. -/
def toFinPerm :
    PermutationalWreathProduct D Q (Fin s) →*
      Equiv.Perm (Fin (u * s)) :=
  finProdFinEquiv.permCongrHom.toMonoidHom.comp
    (toPerm (D := D) (Q := Q) (I := Fin s) (Lambda := Fin u))

theorem toFinPerm_injective [FaithfulSMul D (Fin u)]
    [FaithfulSMul Q (Fin s)] [Nonempty (Fin u)] [Nonempty (Fin s)] :
    Function.Injective (toFinPerm (u := u) (s := s) D Q) :=
  finProdFinEquiv.permCongrHom.injective.comp toPerm_injective

end FiniteDegree

end PermutationalWreathProduct
end SymmetricSubgroupAsymptotics

end
