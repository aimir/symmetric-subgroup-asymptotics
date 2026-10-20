import SymmetricSubgroupAsymptotics.FiniteAbelianSquareKernelQuotient
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Basic

/-! The actual two-torsion of c cyclic-four coordinates has exactly c
binary coordinates. The finite receipts involve only C4 and C2. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.C4SquareKernelCoordinates
abbrev C4 := Multiplicative (ZMod 4)
abbrev C2 := Multiplicative (ZMod 2)

def oneCoordinate : (powMonoidHom (α := C4) 2).ker ≃ C2 where
  toFun z := Multiplicative.ofAdd ((z.val.toAdd.val/2 : ℕ) : ZMod 2)
  invFun x := ⟨Multiplicative.ofAdd (2*(x.toAdd.val : ZMod 4)),by
    change (Multiplicative.ofAdd (2*(x.toAdd.val : ZMod 4)))^2=1
    revert x
    decide +kernel⟩
  left_inv z := by
    apply Subtype.ext
    have hz := z.property
    change z.val^2=1 at hz
    change Multiplicative.ofAdd (2*(((z.val.toAdd.val/2 : ℕ) : ZMod 2).val : ZMod 4))=z.val
    generalize z.val = v at hz ⊢
    revert hz
    revert v
    decide +kernel
  right_inv x := by
    change Multiplicative.ofAdd
      (((2*(x.toAdd.val : ZMod 4)).val/2 : ℕ) : ZMod 2)=x
    revert x
    decide +kernel

def coordinates (c : ℕ) :
    (powMonoidHom (α := Fin c → C4) 2).ker ≃ (Fin c → C2) where
  toFun z i := oneCoordinate ⟨z.val i,congrFun z.property i⟩
  invFun v := ⟨fun i => (oneCoordinate.symm (v i)).val,by
    funext i
    exact (oneCoordinate.symm (v i)).property⟩
  left_inv z := by
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (oneCoordinate.symm_apply_apply ⟨z.val i,congrFun z.property i⟩)
  right_inv v := by
    funext i
    exact oneCoordinate.apply_symm_apply (v i)

 theorem square_kernel_card_le {Z : Type} [CommGroup Z] [Finite Z] {c : ℕ}
    (e : Z →* (Fin c → C4)) (he : Function.Injective e) :
    Nat.card (powMonoidHom (α := Z) 2).ker≤2^c := by
  let f : (powMonoidHom (α := Z) 2).ker →
      (powMonoidHom (α := Fin c → C4) 2).ker := fun z =>
    ⟨e z.val,by
      have hz : z.val^2=1 := z.property
      change (e z.val)^2=1
      rw [←map_pow,hz,map_one]⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact he (congrArg Subtype.val h)
  have hc := Nat.card_le_card_of_injective f hf
  have ht : Nat.card (powMonoidHom (α := Fin c → C4) 2).ker=2^c := by
    rw [Nat.card_congr (coordinates c),Nat.card_fun,Nat.card_congr Multiplicative.toAdd]
    simp
  exact hc.trans_eq ht

end SymmetricSubgroupAsymptotics.C4SquareKernelCoordinates
