import SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergWords
import SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergCoordinates
import SymmetricSubgroupAsymptotics.CFSGSymplecticElementaryProjectiveCenter
import SymmetricSubgroupAsymptotics.CFSGHeisenbergKernelRigidity

/-! The dimension-uniform coordinate Heisenberg group maps into the
SAME original elementary symplectic group by actual transvection words.
Its actual central parameter maps to the original first long-root word
with parameter -2c; hence the actual projective map is injective in odd
characteristic. No parabolic recognition is an input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergUniformEmbedding

open CFSGHeisenbergCoordinateGroup CFSGSymplecticSerreMatrices
open CFSGSymplecticTransvectionGeometry CFSGSymplecticHeisenbergOperators
open CFSGSymplecticHeisenbergWords CFSGSymplecticHeisenbergCoordinates
variable (K : Type) [Field K]

private def firstVector (m : ℕ) : Index (m + 1) → K := Pi.single (Sum.inl 0) 1

def elementaryHom (m : ℕ) (hm : 0 < m) : Element K m →* elementaryRootGroup K (m + 1) where
  toFun g := shearElement K m hm (firstVector K m) (tailVector g) (longParameter g)
  map_one' := by
    apply elementary_ext_of_mulVec K
    intro x
    change ((shearElement K m hm (firstVector K m)
      (tailVector (1 : Element K m)) (longParameter (1 : Element K m))).val : Mat K (m + 1)) *ᵥ x =
        (1 : Mat K (m + 1)) *ᵥ x
    rw [shearElement_apply, tailVector_one, longParameter_one, shear_zero_vector,
      transvection_zero, Matrix.one_mulVec]
    rfl
  map_mul' g h := by
    change shearElement K m hm (firstVector K m) (tailVector (g * h)) (longParameter (g * h)) =
      shearElement K m hm (firstVector K m) (tailVector g) (longParameter g) *
        shearElement K m hm (firstVector K m) (tailVector h) (longParameter h)
    rw [tailVector_mul, longParameter_mul]
    exact (shearElement_mul K m hm (firstVector K m) (tailVector g) (tailVector h)
      (longParameter g) (longParameter h)
      (tailVector_orthogonal_first g) (tailVector_orthogonal_first h)).symm

theorem elementaryHom_apply (m : ℕ) (hm : 0 < m) (g : Element K m)
    (x : Index (m + 1) → K) :
    ((elementaryHom K m hm g).val : Mat K (m + 1)) *ᵥ x =
      shear (m + 1) (firstVector K m) (tailVector g) (longParameter g) x :=
  shearElement_apply K m hm (firstVector K m) (tailVector g) x (longParameter g)

theorem elementaryHom_central (m : ℕ) (hm : 0 < m) (z : Multiplicative K) :
    elementaryHom K m hm (central z) = firstLongRoot K m (-2 * z.toAdd) := by
  apply elementary_ext_of_mulVec K
  intro x
  rw [elementaryHom_apply, tailVector_central, longParameter_central, shear_zero_vector]
  exact (firstLongRoot_mulVec_eq_transvection m (-2 * z.toAdd) x).symm

theorem central_matrix (m : ℕ) (hm : 0 < m) (z : Multiplicative K) :
    ((elementaryHom K m hm (central z)).val : Mat K (m + 1)) =
      1 + Matrix.single (Sum.inl (0 : Fin (m + 1))) (Sum.inr 0) (-2 * z.toAdd) := by
  rw [elementaryHom_central, firstLongRoot_coe]
  simp only [Matrix.transvection, Matrix.smul_single, smul_eq_mul, mul_one]

def projectiveHom (m : ℕ) (hm : 0 < m) : Element K m →* elementaryProjective K (m + 1) :=
  (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (m + 1)))).comp
    (elementaryHom K m hm)

theorem projective_central_injective (m : ℕ) (hm : 0 < m) (hTwo : (2 : K) ≠ 0) :
    Function.Injective ((projectiveHom K m hm).comp (central (K := K) (m := m))) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro z hz
  apply Subgroup.mem_bot.mpr
  have hc : elementaryHom K m hm (central z) ∈
      Subgroup.center (elementaryRootGroup K (m + 1)) := (QuotientGroup.eq_one_iff _).mp hz
  obtain ⟨s, hs⟩ := (elementaryRootGroup_center_iff_scalar K m _).mp hc
  rw [central_matrix] at hs
  have h02 := congrArg (fun A : Mat K (m + 1) => A (Sum.inl 0) (Sum.inr 0)) hs
  have hz0 : (2 : K) * z.toAdd = 0 := by
    simpa [Matrix.single_apply, Matrix.one_apply] using h02
  have he : z.toAdd = 0 := (mul_eq_zero.mp hz0).resolve_left hTwo
  exact congrArg Multiplicative.ofAdd he

theorem projectiveHom_injective (m : ℕ) (hm : 0 < m) (hTwo : (2 : K) ≠ 0) :
    Function.Injective (projectiveHom K m hm) :=
  CFSGHeisenbergKernelRigidity.injective_of_central (projectiveHom K m hm)
    (projective_central_injective K m hm hTwo)

theorem elementaryHom_injective (m : ℕ) (hm : 0 < m) (hTwo : (2 : K) ≠ 0) :
    Function.Injective (elementaryHom K m hm) := by
  intro g h he
  apply projectiveHom_injective K m hm hTwo
  exact congrArg (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (m + 1)))) he

end SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergUniformEmbedding
