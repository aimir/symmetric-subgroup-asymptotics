import SymmetricSubgroupAsymptotics.PermutationalWreathFinite
import SymmetricSubgroupAsymptotics.ConjugacyClassExtension
import SymmetricSubgroupAsymptotics.ConjugacyClassSubgroupIndexBound
import Mathlib.Tactic.Ring

/-! Two sound bounds on the SAME injective wreath homomorphism. An
actual surjective top projection makes the kernel-cardinality bound
and the image-index bound cancel. No base saturation, splitting,
transitivity or subgroup class monotonicity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.WreathHomClassGeometricMean

variable {A C Q I : Type} [Group A] [Group C] [Group Q] [MulAction Q I]
    [Finite A] [Finite C] [Finite Q] [Finite I]

theorem class_square_le_same_top_wreath
    (f : A →* PermutationalWreathProduct C Q I) (hf : Function.Injective f)
    (hproj : Function.Surjective
      ((PermutationalWreathProduct.rightHom (D := C) (I := I)).comp f)) :
    Nat.card (ConjClasses A)^2 ≤ Nat.card C ^ Nat.card I *
      Nat.card (ConjClasses Q) *
      Nat.card (ConjClasses (PermutationalWreathProduct C Q I)) := by
  let π : A →* Q := (PermutationalWreathProduct.rightHom (D := C) (I := I)).comp f
  let e : A ⧸ π.ker ≃* Q := QuotientGroup.quotientKerEquivOfSurjective π hproj
  have hqcard : Nat.card (A ⧸ π.ker) = Nat.card Q := Nat.card_congr e.toEquiv
  have hker : Nat.card π.ker * Nat.card Q = Nat.card A := by
    have h := π.ker.card_mul_index
    rw [Subgroup.index_eq_card,hqcard] at h
    exact h
  have himage : Nat.card f.range = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  have hindex : Nat.card A * f.range.index = Nat.card C ^ Nat.card I * Nat.card Q := by
    have h := f.range.card_mul_index
    rw [himage,PermutationalWreathProduct.natCard_eq] at h
    exact h
  have hcancel : Nat.card π.ker * f.range.index = Nat.card C ^ Nat.card I := by
    have he : (Nat.card π.ker * f.range.index) * Nat.card Q =
        Nat.card C ^ Nat.card I * Nat.card Q := by
      calc
        (Nat.card π.ker * f.range.index) * Nat.card Q =
            (Nat.card π.ker * Nat.card Q) * f.range.index := by ring
        _ = Nat.card A * f.range.index := by rw [hker]
        _ = Nat.card C ^ Nat.card I * Nat.card Q := hindex
    exact Nat.le_antisymm
      (Nat.le_of_mul_le_mul_right he.le (Nat.card_pos (α := Q)))
      (Nat.le_of_mul_le_mul_right he.ge (Nat.card_pos (α := Q)))
  have hquot : Nat.card (ConjClasses (A ⧸ π.ker)) ≤ Nat.card (ConjClasses Q) :=
    Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)
  have hfirst : Nat.card (ConjClasses A) ≤ Nat.card π.ker * Nat.card (ConjClasses Q) :=
    (conjugacyClass_card_le_normal_mul_quotient π.ker).trans
      (Nat.mul_le_mul (Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective) hquot)
  have hsecond := ConjugacyClassSubgroupIndexBound.class_card_le_injective_index f hf
  calc
    Nat.card (ConjClasses A)^2 ≤
        (Nat.card π.ker * Nat.card (ConjClasses Q)) *
          (f.range.index * Nat.card (ConjClasses (PermutationalWreathProduct C Q I))) := by
      simpa only [pow_two] using Nat.mul_le_mul hfirst hsecond
    _ = (Nat.card π.ker * f.range.index) * Nat.card (ConjClasses Q) *
        Nat.card (ConjClasses (PermutationalWreathProduct C Q I)) := by ring
    _ = _ := by rw [hcancel]

end SymmetricSubgroupAsymptotics.WreathHomClassGeometricMean
