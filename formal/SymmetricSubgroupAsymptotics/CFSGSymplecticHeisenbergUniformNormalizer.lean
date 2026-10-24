import SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergUniformEmbedding
import SymmetricSubgroupAsymptotics.CFSGSymplecticUniformTail
import SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergShearEquivariance
import SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergVectorAction
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.FieldSimp

/-! The literal smaller elementary symplectic group normalizes the
actual dimension-uniform Heisenberg subgroup. The quotient action is
the actual natural action in coordinates (b,-a); the central correction
is divided by two only under the explicit odd-characteristic premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergUniformNormalizer

open CFSGHeisenbergCoordinateGroup CFSGSymplecticSerreMatrices
open CFSGSymplecticStabilizerCoordinates CFSGSymplecticHeisenbergCoordinates
open CFSGSymplecticHeisenbergUniformEmbedding CFSGSymplecticUniformTail
open CFSGSymplecticHeisenbergVectorAction CFSGSymplecticHeisenbergWords
open CFSGSymplecticHeisenbergShearEquivariance
variable (K : Type) [Field K]

local instance normalizerVectorActionInstance (m : ℕ) :
    MulAction (elementaryRootGroup K m) ((Fin m → K) × (Fin m → K)) := vectorAction K m

def transform (m : ℕ) (A : elementaryRootGroup K m) (g : Element K m) : Element K m :=
  let v := A • (g.a, g.b)
  ⟨v.1, v.2, g.c + (dot v.1 v.2 - dot g.a g.b) / 2⟩

theorem transform_vector (m : ℕ) (A : elementaryRootGroup K m) (g : Element K m) :
    ((transform K m A g).a, (transform K m A g).b) = A • (g.a, g.b) := rfl

theorem transform_tailVector (m : ℕ) (A : elementaryRootGroup K m) (g : Element K m) :
    tailVector (transform K m A g) =
      ((tailHom K m A).val : Mat K (m + 1)) *ᵥ tailVector g := by
  change tailExtend m (vectorEquiv K m (A • (g.a, g.b))) =
    ((tailHom K m A).val : Mat K (m + 1)) *ᵥ
      tailExtend m (vectorEquiv K m (g.a, g.b))
  rw [vectorAction_apply, (vectorEquiv K m).apply_symm_apply]
  exact (tailHom_tailExtend K m A (vectorEquiv K m (g.a, g.b))).symm

theorem transform_longParameter (m : ℕ) (hTwo : (2 : K) ≠ 0)
    (A : elementaryRootGroup K m) (g : Element K m) :
    longParameter (transform K m A g) = longParameter g := by
  let v := A • (g.a, g.b)
  change dot v.1 v.2 - 2 * (g.c + (dot v.1 v.2 - dot g.a g.b) / 2) =
    dot g.a g.b - 2 * g.c
  field_simp [hTwo]
  ring

theorem tailHom_conjugation (m : ℕ) (hm : 0 < m) (hTwo : (2 : K) ≠ 0)
    (A : elementaryRootGroup K m) (g : Element K m) :
    tailHom K m A * elementaryHom K m hm g * (tailHom K m A)⁻¹ =
      elementaryHom K m hm (transform K m A g) := by
  change tailHom K m A *
      shearElement K m hm (Pi.single (Sum.inl 0) 1) (tailVector g) (longParameter g) *
        (tailHom K m A)⁻¹ =
    shearElement K m hm (Pi.single (Sum.inl 0) 1)
      (tailVector (transform K m A g)) (longParameter (transform K m A g))
  rw [shearElement_conjugate m hm (tailHom K m A) (Pi.single (Sum.inl 0) 1)
    (tailVector g) (longParameter g) (tailHom_fixes_firstPair K m A).1
    (tailVector_orthogonal_first g), ← transform_tailVector,
    transform_longParameter K m hTwo]

theorem tailHom_range_normalizes (m : ℕ) (hm : 0 < m) (hTwo : (2 : K) ≠ 0) :
    (tailHom K m).range ≤ Subgroup.normalizer
      ((elementaryHom K m hm).range : Set (elementaryRootGroup K (m + 1))) := by
  have hforward (A : elementaryRootGroup K m) (g : elementaryRootGroup K (m + 1))
      (hg : g ∈ (elementaryHom K m hm).range) :
      tailHom K m A * g * (tailHom K m A)⁻¹ ∈ (elementaryHom K m hm).range := by
    obtain ⟨h, rfl⟩ := hg
    exact ⟨transform K m A h, (tailHom_conjugation K m hm hTwo A h).symm⟩
  rintro t ⟨A, rfl⟩
  apply Subgroup.mem_normalizer_iff.mpr
  intro g
  constructor
  · exact hforward A g
  · intro hg
    have hh := hforward A⁻¹ _ hg
    simpa only [map_inv, inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh

end SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergUniformNormalizer
