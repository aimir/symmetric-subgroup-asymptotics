import SymmetricSubgroupAsymptotics.CFSGTwistedDNaturalFork
import Mathlib.Algebra.Group.Units.Equiv

/-! A genuine diagram--field automorphism of the literal natural D
root group. The exact original fixed/derived-model bridge is separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDNaturalFieldTwist
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDNaturalFork
variable (K : Type) [Field K]

theorem flip_transpose (s : ℕ) (A : Mat K (s + 2)) :
    flipAlgebra K s A.transpose = (flipAlgebra K s A).transpose := by
  ext i j
  rfl

theorem negative_all (s : ℕ) (i : Fin (s + 2)) :
    flipAlgebra K s (negative K (s + 2) i) =
      negative K (s + 2) (CFSG.Models.dTwist i) := by
  rw [negative, flip_transpose, positive_all]
  rfl

theorem rootMatrix_all (s : ℕ) (neg : Bool) (i : Fin (s + 2)) :
    flipAlgebra K s (rootMatrix K (s + 2) neg i) =
      rootMatrix K (s + 2) neg (CFSG.Models.dTwist i) := by
  cases neg
  · simpa only [rootMatrix, Bool.false_eq_true, if_false] using positive_all K s i
  · simpa only [rootMatrix, if_true] using negative_all K s i

theorem flip_map (s : ℕ) (σ : K ≃+* K) (A : Mat K (s + 2)) :
    flipAlgebra K s (σ.toRingHom.mapMatrix A) =
      σ.toRingHom.mapMatrix (flipAlgebra K s A) := by
  ext i j
  rfl

def matrixTwist (s : ℕ) (σ : K ≃+* K) : Mat K (s + 2) ≃+* Mat K (s + 2) :=
  σ.mapMatrix.trans (flipAlgebra K s).toRingEquiv

def unitTwist (s : ℕ) (σ : K ≃+* K) : MulAut ((Mat K (s + 2))ˣ) :=
  Units.mapEquiv (matrixTwist K s σ).toMulEquiv

theorem matrixTwist_root (s : ℕ) (σ : K ≃+* K) (neg : Bool)
    (i : Fin (s + 2)) (t : K) :
    matrixTwist K s σ (rootTransvection K (s + 2) neg i t : Mat K (s + 2)) =
      (rootTransvection K (s + 2) neg (CFSG.Models.dTwist i) (σ t) : Mat K (s + 2)) := by
  have hs (a : K) (M : Mat K (s + 2)) : σ.toRingHom.mapMatrix (a • M) =
      σ a • σ.toRingHom.mapMatrix M := by
    ext x y
    exact σ.map_mul a (M x y)
  change flipAlgebra K s (σ.toRingHom.mapMatrix (1 + t • rootMatrix K (s + 2) neg i)) = _
  rw [map_add, map_one, hs, map_rootMatrix, map_add, map_one, map_smul, rootMatrix_all]
  rfl

theorem unitTwist_root (s : ℕ) (σ : K ≃+* K) (neg : Bool)
    (i : Fin (s + 2)) (t : K) :
    unitTwist K s σ (rootTransvection K (s + 2) neg i t) =
      rootTransvection K (s + 2) neg (CFSG.Models.dTwist i) (σ t) := by
  apply Units.ext
  exact matrixTwist_root K s σ neg i t

theorem elementary_map_eq (s : ℕ) (σ : K ≃+* K) :
    (elementaryRootGroup K (s + 2)).map (unitTwist K s σ).toMonoidHom =
      elementaryRootGroup K (s + 2) := by
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro u ⟨neg, i, t, rfl⟩
    change unitTwist K s σ _ ∈ elementaryRootGroup K (s + 2)
    rw [unitTwist_root]
    exact rootTransvection_mem K (s + 2) neg _ _
  · apply (Subgroup.closure_le _).mpr
    rintro u ⟨neg, i, t, rfl⟩
    refine ⟨rootTransvection K (s + 2) neg (CFSG.Models.dTwist i) (σ.symm t),
      rootTransvection_mem K (s + 2) neg _ _, ?_⟩
    change unitTwist K s σ _ = _
    rw [unitTwist_root, CFSGSerreDiagram.dTwist_involutive,
      RingEquiv.apply_symm_apply]

def naturalAutomorphism (s : ℕ) (σ : K ≃+* K) :
    MulAut (elementaryRootGroup K (s + 2)) :=
  ((unitTwist K s σ).subgroupMap (elementaryRootGroup K (s + 2))).trans
    (MulEquiv.subgroupCongr (elementary_map_eq K s σ))

end SymmetricSubgroupAsymptotics.CFSGTwistedDNaturalFieldTwist
