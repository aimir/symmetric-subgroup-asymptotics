import SymmetricSubgroupAsymptotics.PermutationalWreathProduct
import SymmetricSubgroupAsymptotics.TwoBinaryThreePermutationCoordinates

/-! The actual kernel of the two-head wreath projection embeds in the
physical six-coordinate vector group. Conjugation is the actual retained
top permutation; no splitting of a subgroup extension is required. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwoBinaryThreeWreathKernel

abbrev Bits := ZMod 2 × ZMod 2
abbrev Wreath (T : Subgroup (Equiv.Perm (Fin 3))) :=
  PermutationalWreathProduct (Multiplicative Bits) T (Fin 3)
abbrev top (T : Subgroup (Equiv.Perm (Fin 3))) : Wreath T →* T :=
  PermutationalWreathProduct.rightHom

variable (T : Subgroup (Equiv.Perm (Fin 3)))

def base : (top T).ker →* (Fin 3 → Multiplicative Bits) where
  toFun k := k.val.left
  map_one' := rfl
  map_mul' a b := by
    have ha : a.val.right=1 := a.property
    funext i
    change a.val.left i*b.val.left (a.val.right⁻¹ • i)=a.val.left i*b.val.left i
    rw [ha]
    simp

theorem base_injective : Function.Injective (base T) := by
  intro a b h
  apply Subtype.ext
  apply PermutationalWreathProduct.ext h
  exact a.property.trans b.property.symm

/-- Both binary heads are kept, in their original physical order. -/
def flatten : (Fin 3 → Multiplicative Bits) →*
    Multiplicative TwoBinaryThreePermutationCoordinates.Vector where
  toFun v := Multiplicative.ofAdd (fun x => if x.1=0 then (v x.2).toAdd.1
    else (v x.2).toAdd.2)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext x
    simp
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    funext x
    by_cases h : x.1=0 <;> simp [h]

theorem flatten_injective : Function.Injective flatten := by
  intro a b h
  funext i
  apply Multiplicative.toAdd.injective
  apply Prod.ext
  · exact congrArg (fun v : Multiplicative TwoBinaryThreePermutationCoordinates.Vector =>
      v.toAdd (0,i)) h
  · exact congrArg (fun v : Multiplicative TwoBinaryThreePermutationCoordinates.Vector =>
      v.toAdd (1,i)) h

def vector : (top T).ker →* Multiplicative TwoBinaryThreePermutationCoordinates.Vector :=
  flatten.comp (base T)

theorem vector_injective : Function.Injective (vector T) :=
  flatten_injective.comp (base_injective T)

/-- The original base part cancels in conjugation because each physical
head is abelian. The actual top, rather than a surrogate C3 quotient,
acts on the retained vector. -/
theorem conjugate_left (g : Wreath T) (k : (top T).ker) (i : Fin 3) :
    (MulAut.conjNormal g k).val.left i=k.val.left (g.right⁻¹ • i) := by
  have hk : k.val.right=1 := k.property
  change (g*k.val*g⁻¹).left i=_
  simp only [PermutationalWreathProduct.mul_left,
    PermutationalWreathProduct.mul_right, PermutationalWreathProduct.inv_left,
    Pi.mul_apply, Pi.inv_apply]
  rw [hk]
  simp only [mul_one, inv_smul_smul]
  exact mul_right_comm _ _ _ |>.trans (by simp)

theorem vector_conjugate (g : Wreath T) (k : (top T).ker) :
    (vector T (MulAut.conjNormal g k)).toAdd=
      TwoBinaryThreePermutationCoordinates.representation T g.right (vector T k).toAdd := by
  funext x
  change (if x.1=0 then ((MulAut.conjNormal g k).val.left x.2).toAdd.1
    else ((MulAut.conjNormal g k).val.left x.2).toAdd.2)=_
  rw [conjugate_left]
  rfl

end SymmetricSubgroupAsymptotics.TwoBinaryThreeWreathKernel
