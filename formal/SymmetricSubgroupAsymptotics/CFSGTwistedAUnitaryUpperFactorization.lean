import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperCompression
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRadicalMiddleAction

/-! Exact recursive factorization of the ACTUAL upper subgroup into its
actual outer radical and literal embedded smaller upper subgroup. The
same factorization is transported to the ORIGINAL fixed source. It does
not assume derived membership in a small SU3(2) induction base. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryUpperArrays
open CFSGTwistedAUpperUnipotent

def upperFixedHom (q : CFSG.PrimePower) (r : ℕ) : naturalUnipotent r q →* naturalFixed r q where
  toFun g := ⟨g.val, g.property.2⟩
  map_one' := Subtype.ext rfl
  map_mul' g h := Subtype.ext rfl

theorem upper_radical_middle_factor (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalUnipotent (s + 2) q) :
    ∃ r : fixedRadical q s,
      upperFixedHom q (s + 2) g = r.val *
        naturalFixedMiddleHom q s (upperFixedHom q s (middleUnipotentElement q s g)) := by
  let A := (middleNaturalElement q s g).val
  let w : Fin (s + 1) → q.Extension 2 := fun i =>
    (g.val.val : Mat (q.Extension 2) (s + 2)) 0 (middleIndex s i)
  let v : Fin (s + 1) → q.Extension 2 := fun i =>
    (g.val.val : Mat (q.Extension 2) (s + 2)) (middleIndex s i) (Fin.last (s + 2))
  let b : q.Extension 2 := (g.val.val : Mat (q.Extension 2) (s + 2)) 0 (Fin.last (s + 2))
  let m := naturalFixedMiddleHom q s (upperFixedHom q s (middleUnipotentElement q s g))
  have hshape : (blockFixedMatrixHom q s (upperFixedHom q (s + 2) g) :
      Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) (q.Extension 2)) =
        upperMiddleArray w (A : Mat (q.Extension 2) s) v b :=
    upper_block_shape s (g.val.val : Mat (q.Extension 2) (s + 2)) g.property.1.1 g.property.1.2
  have hraw : blockFixedMatrixHom q s (upperFixedHom q (s + 2) g) * (middleUnit A)⁻¹ =
      upperUnit (w ᵥ* ((A⁻¹ : (Mat (q.Extension 2) s)ˣ) : Mat (q.Extension 2) s)) v b := by
    apply Units.ext
    change (blockFixedMatrixHom q s (upperFixedHom q (s + 2) g) :
      Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) (q.Extension 2)) *
        middleArray ((A⁻¹ : (Mat (q.Extension 2) s)ˣ) : Mat (q.Extension 2) s) = _
    rw [hshape, upperMiddleArray_factor w v b A, mul_assoc, ← middleArray_mul,
      Units.mul_inv, middleArray_one, mul_one]
    all_goals rfl
  have hr : upperFixedHom q (s + 2) g * m⁻¹ ∈ fixedRadical q s := by
    change blockFixedMatrixHom q s (upperFixedHom q (s + 2) g * m⁻¹) ∈ arrayGroup
    rw [map_mul, map_inv]
    have hm : blockFixedMatrixHom q s m = middleUnit A :=
      blockFixedMatrixHom_middle q s (upperFixedHom q s (middleUnipotentElement q s g))
    rw [hm, hraw]
    exact ⟨w ᵥ* ((A⁻¹ : (Mat (q.Extension 2) s)ˣ) : Mat (q.Extension 2) s), v, b, rfl⟩
  refine ⟨⟨upperFixedHom q (s + 2) g * m⁻¹, hr⟩, ?_⟩
  change upperFixedHom q (s + 2) g = (upperFixedHom q (s + 2) g * m⁻¹) * m
  simp only [mul_assoc, inv_mul_cancel, mul_one]

theorem original_upper_radical_middle_factor (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalUnipotent (s + 2) q) :
    ∃ r : fixedRadical q s,
      unipotentToOriginalFixed (s + 2) q g = radicalToOriginal q s r *
        naturalFixedToOriginal q (s + 2)
          (naturalFixedMiddleHom q s (upperFixedHom q s (middleUnipotentElement q s g))) := by
  obtain ⟨r, hr⟩ := upper_radical_middle_factor q s g
  refine ⟨r, ?_⟩
  have h := congrArg (naturalFixedToOriginal q (s + 2)) hr
  rw [map_mul] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
