import SymmetricSubgroupAsymptotics.TwoBinaryThreeWreathKernel

/-! The physical head base detects every nontrivial element of the
retained top. This uses actual single-coordinate vectors and does not
replace the retained top by a cubic quotient. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TwoBinaryThreeWreathKernel

variable (T : Subgroup (Equiv.Perm (Fin 3)))

/-- Centralizing every physical kernel vector forces trivial actual top. -/
theorem right_eq_one_of_centralizes_kernel (g : Wreath T)
    (h : ∀ k : (top T).ker,g*k.val=k.val*g) : g.right=1 := by
  have hpoint (i : Fin 3) : (g.right⁻¹ : T) • i=i := by
    by_contra hi
    let a : Multiplicative Bits := Multiplicative.ofAdd (1,0)
    have ha : a≠1 := by decide +kernel
    let k : (top T).ker := ⟨⟨fun j => if j=i then a else 1,1⟩,rfl⟩
    have hc : MulAut.conjNormal g k=k := by
      apply Subtype.ext
      change g*k.val*g⁻¹=k.val
      rw [h k]
      simp [mul_assoc]
    have hv := congrArg (fun z : (top T).ker => z.val.left i) hc
    change (MulAut.conjNormal g k).val.left i=k.val.left i at hv
    have heval : k.val.left (g.right⁻¹ • i)=k.val.left i :=
      (conjugate_left T g k i).symm.trans hv
    clear hv
    have hv := heval

    change (if (g.right⁻¹ : T) • i=i then a else 1)=
      (if i=i then a else 1) at hv
    rw [if_neg hi,if_pos rfl] at hv
    exact ha hv.symm
  apply Subtype.ext
  apply Equiv.ext
  intro i
  have hi := hpoint ((g.right : Equiv.Perm (Fin 3)) i)
  change (g.right : Equiv.Perm (Fin 3)).symm
    ((g.right : Equiv.Perm (Fin 3)) i)=(g.right : Equiv.Perm (Fin 3)) i at hi
  rw [Equiv.symm_apply_apply] at hi
  exact hi.symm

end SymmetricSubgroupAsymptotics.TwoBinaryThreeWreathKernel
