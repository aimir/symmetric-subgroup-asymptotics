import SymmetricSubgroupAsymptotics.PrimeSectionalCharacterRank
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.ZMod.Basic
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneAugmentationTranslations
abbrev Plane := Fin 2 → ZMod 2
abbrev Model := Multiplicative (Fin 2 → Plane)
abbrev Point := Plane × Fin 3

def shift (v : Model) : Fin 3 → Plane :=
  ![v.toAdd 0,v.toAdd 1,-v.toAdd 0-v.toAdd 1]
private theorem shift_one (i : Fin 3) : shift 1 i=0 := by
  fin_cases i <;> simp [shift]
private theorem shift_mul (v w : Model) (i : Fin 3) : shift (v*w) i=shift v i+shift w i := by
  fin_cases i <;> simp [shift] <;> abel

def translation (v : Model) : Equiv.Perm Point where
  toFun x := (x.1+shift v x.2,x.2)
  invFun x := (x.1-shift v x.2,x.2)
  left_inv x := by
    rcases x with ⟨a,i⟩
    apply Prod.ext
    · change a+shift v i-shift v i=a
      abel
    · rfl
  right_inv x := by
    rcases x with ⟨a,i⟩
    apply Prod.ext
    · change a-shift v i+shift v i=a
      abel
    · rfl

def hom : Model →* Equiv.Perm Point where
  toFun := translation
  map_one' := by
    apply Equiv.ext
    rintro ⟨a,i⟩
    apply Prod.ext
    · change a+shift 1 i=a
      rw [shift_one,add_zero]
    · rfl
  map_mul' v w := by
    apply Equiv.ext
    rintro ⟨a,i⟩
    apply Prod.ext
    · change a+shift (v*w) i=(a+shift w i)+shift v i
      rw [shift_mul]
      abel
    · rfl

theorem hom_injective : Function.Injective hom := by
  intro v w h
  apply Multiplicative.toAdd.injective
  funext i
  have he (j : Fin 3) := congrArg (fun p : Equiv.Perm Point => (p (0,j)).1) h
  fin_cases i
  · simpa [hom,translation,shift] using he 0
  · simpa [hom,translation,shift] using he 1

def action (e : Point ≃ Fin 12) : Model →* Equiv.Perm (Fin 12) :=
  e.permCongrHom.toMonoidHom.comp hom

theorem action_injective (e : Point ≃ Fin 12) : Function.Injective (action e) :=
  e.permCongrHom.injective.comp hom_injective

end SymmetricSubgroupAsymptotics.BinaryPlaneAugmentationTranslations
