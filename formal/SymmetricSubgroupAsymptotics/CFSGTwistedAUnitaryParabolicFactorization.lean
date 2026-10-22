import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryParabolicCompression
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperFactorization

/-! Every actual defining-fixed matrix fixing e0 factors as an ACTUAL
upper element times the literal embedding of a smaller defining-fixed
matrix. This is an unconditional Gaussian step, retaining determinant1
and the original signed form in the middle block. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryUpperArrays
open CFSGTwistedAUpperUnipotent

theorem fixedRadical_mem_upper (q : CFSG.PrimePower) (s : ℕ) (g : fixedRadical q s) :
    g.val.val ∈ naturalUnipotent (s + 2) q := by
  obtain ⟨hd, hs⟩ := (mem_fixedRadical_iff_natural_support q s g.val).mp g.property
  refine ⟨⟨?_, hd⟩, g.val.property⟩
  intro i j hij
  have hi0 : i ≠ 0 := by
    intro he
    subst i
    change j.val < 0 at hij
    omega
  have hjl : j ≠ Fin.last (s + 2) := by
    intro he
    subst j
    change s + 2 < i.val at hij
    have hi := i.isLt
    omega
  have hne : i ≠ j := ne_of_gt hij
  change (g.val.val.val : Mat (q.Extension 2) (s + 2)) i j = 0
  rw [hs i j hi0 hjl, Matrix.one_apply, if_neg hne]

theorem normalized_radical_middle_factor (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 2) q)
    (hcol : (fun i => (g.val.val : Mat (q.Extension 2) (s + 2)) i 0) = Pi.single 0 1) :
    ∃ u : naturalUnipotent (s + 2) q, ∃ m : naturalFixed s q,
      g = upperFixedHom q (s + 2) u * naturalFixedMiddleHom q s m := by
  let A := (normalizedMiddleNatural q s g hcol).val
  let w : Fin (s + 1) → q.Extension 2 := fun i =>
    (g.val.val : Mat (q.Extension 2) (s + 2)) 0 (middleIndex s i)
  let v : Fin (s + 1) → q.Extension 2 := fun i =>
    (g.val.val : Mat (q.Extension 2) (s + 2)) (middleIndex s i) (Fin.last (s + 2))
  let b : q.Extension 2 := (g.val.val : Mat (q.Extension 2) (s + 2)) 0 (Fin.last (s + 2))
  let m := normalizedMiddleFixed q s g hcol
  let M := naturalFixedMiddleHom q s m
  have hshape : (blockFixedMatrixHom q s g :
      Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) (q.Extension 2)) =
      upperMiddleArray w (A : Mat (q.Extension 2) s) v b :=
    normalized_block_shape q s g hcol
  have hraw : blockFixedMatrixHom q s g * (middleUnit A)⁻¹ =
      upperUnit (w ᵥ* ((A⁻¹ : (Mat (q.Extension 2) s)ˣ) : Mat (q.Extension 2) s)) v b := by
    apply Units.ext
    change (blockFixedMatrixHom q s g :
      Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) (q.Extension 2)) *
        middleArray ((A⁻¹ : (Mat (q.Extension 2) s)ˣ) : Mat (q.Extension 2) s) = _
    rw [hshape, upperMiddleArray_factor w v b A, mul_assoc, ← middleArray_mul,
      Units.mul_inv, middleArray_one, mul_one]
    all_goals rfl
  have hr : g * M⁻¹ ∈ fixedRadical q s := by
    change blockFixedMatrixHom q s (g * M⁻¹) ∈ arrayGroup
    rw [map_mul, map_inv]
    have hM : blockFixedMatrixHom q s M = middleUnit A := blockFixedMatrixHom_middle q s m
    rw [hM, hraw]
    exact ⟨w ᵥ* ((A⁻¹ : (Mat (q.Extension 2) s)ˣ) : Mat (q.Extension 2) s), v, b, rfl⟩
  let r : fixedRadical q s := ⟨g * M⁻¹, hr⟩
  let u : naturalUnipotent (s + 2) q := ⟨r.val.val, fixedRadical_mem_upper q s r⟩
  refine ⟨u, m, ?_⟩
  change g = (g * M⁻¹) * M
  simp only [mul_assoc, inv_mul_cancel, mul_one]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
