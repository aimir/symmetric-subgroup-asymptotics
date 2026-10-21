import SymmetricSubgroupAsymptotics.BinaryCommonEightShearOriginalMembership

/-! The four Boolean translations are elements of the original zero
model on its original points. Later lifts through an outer pair action
may have arbitrary affine offsets. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U (Fin 8))

theorem canonicalPointLabels_affinePermutation (t : Equiv.Perm (Fin 8))
    (a : Fin 8 → ZMod 2) (x : X) :
    F.canonicalPointLabels (F.affinePermutation t a x) =
      binaryEightCanonicalPairFrame.affinePermutation t a (F.canonicalPointLabels x) := by
  obtain ⟨⟨i, b⟩, rfl⟩ := F.frame.surjective x
  rw [F.affinePermutation_apply_frame]
  simp only [canonicalPointLabels, Equiv.trans_apply, Equiv.symm_apply_apply]
  change binaryEightPairPointLabels (t i, b + a (t i)) =
    binaryEightCanonicalPairFrame.affinePermutation t a (binaryEightPairPointLabels (i, b))
  exact (binaryEightCanonicalPairFrame.affinePermutation_apply_frame t a i b).symm

def commonBooleanPointLabels : X ≃ Fin 16 :=
  F.canonicalPointLabels.trans BinaryCommonEightShearCoordinates.pointLabels.symm

def commonTranslationRow (hzero : U = F.splitAffineAction)
    (hreg : ∀ j : Fin 3, BinaryMenuCayley8T3.generators j ∈ F.top.range)
    (hconst : (fun _ : Fin 8 => (1 : ZMod 2)) ∈ F.kernelSpace) (i : Fin 4) : U :=
  Fin.cases (F.originalZeroRow hzero 1 (fun _ => 1) hconst)
    (fun j => F.originalZeroRow hzero ⟨_, hreg j⟩ 0 F.kernelSpace.zero_mem) i

theorem commonTranslationRow_pointLabels (hzero : U = F.splitAffineAction)
    (hreg : ∀ j : Fin 3, BinaryMenuCayley8T3.generators j ∈ F.top.range)
    (hconst : (fun _ : Fin 8 => (1 : ZMod 2)) ∈ F.kernelSpace)
    (i : Fin 4) (x : X) :
    F.commonBooleanPointLabels (F.commonTranslationRow hzero hreg hconst i • x) =
      BinaryBooleanFourPolynomialCoordinates.flipIndex i (F.commonBooleanPointLabels x) := by
  have hi : F.canonicalPointLabels (F.commonTranslationRow hzero hreg hconst i • x) =
      BinaryCommonEightShearCoordinates.originalTranslation i (F.canonicalPointLabels x) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact F.canonicalPointLabels_affinePermutation 1 (fun _ => 1) x
    · exact F.canonicalPointLabels_affinePermutation (BinaryMenuCayley8T3.generators j) 0 x
  change BinaryCommonEightShearCoordinates.pointLabels.symm
    (F.canonicalPointLabels (F.commonTranslationRow hzero hreg hconst i • x)) = _
  rw [hi]
  have hh := BinaryCommonEightShearCoordinates.originalTranslation_pointLabels i
    (BinaryCommonEightShearCoordinates.pointLabels.symm (F.canonicalPointLabels x))
  rw [Equiv.apply_symm_apply] at hh
  rw [hh, Equiv.symm_apply_apply]
  rfl

end SymmetricSubgroupAsymptotics.BinaryPairFrame
