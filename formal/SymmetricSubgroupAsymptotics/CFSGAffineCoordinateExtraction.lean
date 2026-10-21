import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.GroupTheory.Perm.Basic

/-! An actual affine permutation preserving coordinate fibres has literal
one-variable coordinate permutations. A preserved diagonal identifies them. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGAffineCoordinateExtraction
variable {F n : Type*} [Field F] [DecidableEq n]

variable (f : Equiv.Perm (n→F))
    (hf : ∀(v w : n→F)(i : n),f v i=f w i↔v i=w i)

def coordinateEquiv (i : n) : F≃F :=
  Equiv.ofBijective (fun a => f (Pi.single i a) i) (by
    constructor
    · intro a b hab
      have hh := (hf (Pi.single i a) (Pi.single i b) i).mp hab
      simpa only [Pi.single_eq_same] using hh
    · intro a
      let v := f.symm (Pi.single i a)
      refine ⟨v i,?_⟩
      have hh := (hf (Pi.single i (v i)) v i).mpr (by simp)
      simpa only [v,Equiv.apply_symm_apply,Pi.single_eq_same] using hh)

theorem apply_coordinate (v : n→F) (i : n) : f v i=coordinateEquiv f hf i (v i) := by
  exact ((hf (Pi.single i (v i)) v i).mpr (by simp)).symm

@[simp] theorem coordinateEquiv_zero (h0 : f 0=0) (i : n) :
    coordinateEquiv f hf i 0=0 := by
  change f (Pi.single i 0) i=0
  simp only [Pi.single_zero,h0,Pi.zero_apply]

@[simp] theorem coordinateEquiv_one (h1 : f (fun _ => 1)=(fun _ => 1)) (i : n) :
    coordinateEquiv f hf i 1=1 := by
  have hh := apply_coordinate f hf (fun _ => 1) i
  rw [h1] at hh
  exact hh.symm

theorem coordinateEquiv_eq (hd : ∀(a : F)(i j : n),f (fun _ => a) i=f (fun _ => a) j)
    (i j : n) : coordinateEquiv f hf i=coordinateEquiv f hf j := by
  apply Equiv.ext
  intro a
  rw [←apply_coordinate f hf (fun _ => a) i,←apply_coordinate f hf (fun _ => a) j]
  exact hd a i j

theorem apply_common_coordinate
    (hd : ∀(a : F)(i j : n),f (fun _ => a) i=f (fun _ => a) j)
    (b : n) (v : n→F) (i : n) : f v i=coordinateEquiv f hf b (v i) := by
  rw [apply_coordinate f hf v i,coordinateEquiv_eq f hf hd i b]

end SymmetricSubgroupAsymptotics.CFSGAffineCoordinateExtraction
