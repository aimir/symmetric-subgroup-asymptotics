import SymmetricSubgroupAsymptotics.CFSGSerreGeneratorRepresentation
import SymmetricSubgroupAsymptotics.CFSGSerreGeneratorExt
import SymmetricSubgroupAsymptotics.CFSGSerreDiagramLattice

/-! The generator exchange E↔F, H↦-H is an ACTUAL involution of the
original rational quotient and preserves its SAME integral lattice. No
finite-type basis, target matrix faithfulness, or simplicity is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreChevalleyInvolution
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence CFSGSerreDiagram
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)

private theorem exchanged_EF (i j : Fin r) :
    ⁅generator A (.F i),generator A (.E j)⁆ =
      if i=j then -generator A (.H i) else 0 := by
  by_cases hij : i=j
  · subst j
    rw [←lie_skew (generator A (.F i)) (generator A (.E i)),generator_EF_same,if_pos rfl]
  · rw [←lie_skew (generator A (.F i)) (generator A (.E j)),generator_EF_ne A j i (Ne.symm hij),neg_zero,if_neg hij]

private theorem exchanged_ad (neg : Bool) (i j : Fin r) :
    (LieAlgebra.ad ℚ (RationalLie A) (rootVector A neg i)^(-A i j).toNat)
      ⁅rootVector A neg i,rootVector A neg j⁆=0 := by
  cases neg
  · simpa only [rootVector, Bool.false_eq_true,if_false,pow_succ,
      Module.End.mul_apply,LieAlgebra.ad_apply] using generator_adE A i j
  · simpa only [rootVector,if_true,pow_succ,
      Module.End.mul_apply,LieAlgebra.ad_apply] using generator_adF A i j

def rationalMap : RationalLie A →ₗ⁅ℚ⁆ RationalLie A :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation
    (fun i => -generator A (.H i))
    (fun i => generator A (.F i)) (fun i => generator A (.E i)) A
    (by intro i j; simp only [lie_neg,neg_lie,neg_neg,generator_HH])
    (exchanged_EF A)
    (by intro i j; rw [neg_lie,generator_HF,neg_neg])
    (by intro i j; rw [neg_lie,generator_HE])
    (exchanged_ad A true) (exchanged_ad A false)

@[simp] theorem rationalMap_H (i : Fin r) :
    rationalMap A (generator A (.H i)) = -generator A (.H i) :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _
@[simp] theorem rationalMap_E (i : Fin r) :
    rationalMap A (generator A (.E i)) = generator A (.F i) :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _
@[simp] theorem rationalMap_F (i : Fin r) :
    rationalMap A (generator A (.F i)) = generator A (.E i) :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _

theorem rationalMap_involutive : Function.Involutive (rationalMap A) := by
  have h : (rationalMap A).comp (rationalMap A) = LieHom.id := by
    apply CFSGSerreGeneratorExt.hom_ext A
    intro g
    cases g <;> simp only [LieHom.comp_apply,rationalMap_H,rationalMap_E,
      rationalMap_F,map_neg,neg_neg,LieHom.id_apply]
  intro x
  exact LieHom.congr_fun h x

@[simp] theorem rationalMap_root (neg : Bool) (i : Fin r) :
    rationalMap A (rootVector A neg i)=rootVector A (!neg) i := by
  cases neg <;> simp [rootVector]

theorem rationalMap_dividedPower (neg : Bool) (i : Fin r) (k : ℕ)
    (x : RationalLie A) :
    rationalMap A (dividedPower A neg i k x)=
      dividedPower A (!neg) i k (rationalMap A x) := by
  change rationalMap A (((k.factorial:ℚ)⁻¹) •
    (LieAlgebra.ad ℚ (RationalLie A) (rootVector A neg i)^k) x) = _
  rw [map_smul,lieHom_ad_pow_apply,rationalMap_root]
  rfl

theorem preserves_lattice (x : RationalLie A) (hx : x∈integralLattice A) :
    rationalMap A x ∈ integralLattice A := by
  let S := (integralLattice A).comap ((rationalMap A).toLinearMap.restrictScalars ℤ)
  have hle : integralLattice A ≤ S := by
    apply integralLattice_le_of_stable A S
    · intro g
      change rationalMap A (generator A g)∈integralLattice A
      cases g with
      | H i => rw [rationalMap_H]; exact Submodule.neg_mem _ (generator_mem_integralLattice A _)
      | E i => rw [rationalMap_E]; exact generator_mem_integralLattice A _
      | F i => rw [rationalMap_F]; exact generator_mem_integralLattice A _
    · intro neg i k y hy
      change rationalMap A (dividedPower A neg i k y)∈integralLattice A
      rw [rationalMap_dividedPower]
      exact dividedPower_mem A (!neg) i k _ hy
  exact hle hx

def integralMap : integralLattice A →ₗ[ℤ] integralLattice A :=
  ((rationalMap A).toLinearMap.restrictScalars ℤ).restrict (preserves_lattice A)

theorem integralMap_involutive : Function.Involutive (integralMap A) := by
  intro x
  apply Subtype.ext
  exact rationalMap_involutive A x.val

end SymmetricSubgroupAsymptotics.CFSGSerreChevalleyInvolution
