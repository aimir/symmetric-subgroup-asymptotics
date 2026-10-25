import SymmetricSubgroupAsymptotics.WreathHomClassGeometricMean

/-! Any actual wreath homomorphism is lifted to its OWN right-projection
range, with the inherited action on the SAME coordinates. The range
projection is surjective by construction; no transitivity is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.WreathHomProjectionRange

variable {A C Q I : Type} [Group A] [Group C] [Group Q] [MulAction Q I]

abbrev topProjection (f : A →* PermutationalWreathProduct C Q I) : A →* Q :=
  (PermutationalWreathProduct.rightHom (D := C) (I := I)).comp f

def rangeLift (f : A →* PermutationalWreathProduct C Q I) :
    A →* PermutationalWreathProduct C (topProjection f).range I where
  toFun a := ⟨(f a).left,(topProjection f).rangeRestrict a⟩
  map_one' := by
    apply PermutationalWreathProduct.ext
    · exact congrArg (fun w : PermutationalWreathProduct C Q I => w.left) (map_one f)
    · exact (topProjection f).rangeRestrict.map_one
  map_mul' a b := by
    apply PermutationalWreathProduct.ext
    · exact congrArg (fun w : PermutationalWreathProduct C Q I => w.left) (map_mul f a b)
    · exact (topProjection f).rangeRestrict.map_mul a b

theorem rangeLift_injective (f : A →* PermutationalWreathProduct C Q I)
    (hf : Function.Injective f) : Function.Injective (rangeLift f) := by
  intro a b he
  apply hf
  apply PermutationalWreathProduct.ext
  · exact congrArg (fun w : PermutationalWreathProduct C (topProjection f).range I => w.left) he
  · exact congrArg (fun w : PermutationalWreathProduct C (topProjection f).range I => w.right.val) he

theorem rangeLift_top_surjective (f : A →* PermutationalWreathProduct C Q I) :
    Function.Surjective ((PermutationalWreathProduct.rightHom
      (D := C) (I := I)).comp (rangeLift f)) := by
  exact (topProjection f).rangeRestrict_surjective

theorem class_square_le_actual_top_range_wreath
    [Finite A] [Finite C] [Finite Q] [Finite I]
    (f : A →* PermutationalWreathProduct C Q I) (hf : Function.Injective f) :
    Nat.card (ConjClasses A)^2 ≤ Nat.card C ^ Nat.card I *
      Nat.card (ConjClasses (topProjection f).range) *
      Nat.card (ConjClasses (PermutationalWreathProduct C (topProjection f).range I)) :=
  WreathHomClassGeometricMean.class_square_le_same_top_wreath
    (rangeLift f) (rangeLift_injective f hf) (rangeLift_top_surjective f)

end SymmetricSubgroupAsymptotics.WreathHomProjectionRange
