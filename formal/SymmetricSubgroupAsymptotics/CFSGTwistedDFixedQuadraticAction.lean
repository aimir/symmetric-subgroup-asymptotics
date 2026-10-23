import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedQuadraticNondegenerate

/-! The SAME literal relative-root group acts faithfully and linearly
on its defining-fixed space over the actual fixed field, preserving
the bundled quadratic form in all characteristics. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedQuadraticAction
open CFSGOrthogonalDSerreMatrices CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDRelativeFixedGroup CFSGTwistedDFixedQuadraticSpace
open CFSGTwistedDFixedQuadraticNondegenerate CFSGTwistedA2FixedField

def fixedLinearEquiv (n : ℕ) (q : CFSG.PrimePower) (g : relativeRootGroup n q) :
    fixedSpace n q ≃ₗ[fixedField q] fixedSpace n q where
  toFun v := ⟨(g.val : Mat (q.Extension 2) (n + 2)) *ᵥ v.val,
    relative_preserves_fixed_vectors n q g v.val v.property⟩
  invFun v := ⟨(↑(g.val⁻¹) : Mat (q.Extension 2) (n + 2)) *ᵥ v.val,
    relative_preserves_fixed_vectors n q g⁻¹ v.val v.property⟩
  left_inv v := by
    apply Subtype.ext
    change (↑(g.val⁻¹) : Mat (q.Extension 2) (n + 2)) *ᵥ
      ((g.val : Mat (q.Extension 2) (n + 2)) *ᵥ v.val) = v.val
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  right_inv v := by
    apply Subtype.ext
    change (g.val : Mat (q.Extension 2) (n + 2)) *ᵥ
      ((↑(g.val⁻¹) : Mat (q.Extension 2) (n + 2)) *ᵥ v.val) = v.val
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  map_add' v w := by
    apply Subtype.ext
    change (g.val : Mat (q.Extension 2) (n + 2)) *ᵥ (v.val + w.val) =
      (g.val : Mat (q.Extension 2) (n + 2)) *ᵥ v.val +
        (g.val : Mat (q.Extension 2) (n + 2)) *ᵥ w.val
    exact Matrix.mulVec_add _ _ _
  map_smul' a v := by
    apply Subtype.ext
    change (g.val : Mat (q.Extension 2) (n + 2)) *ᵥ ((a : q.Extension 2) • v.val) =
      (a : q.Extension 2) • ((g.val : Mat (q.Extension 2) (n + 2)) *ᵥ v.val)
    exact Matrix.mulVec_smul _ _ _

theorem fixedLinearEquiv_apply (n : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup n q) (v : fixedSpace n q) :
    (fixedLinearEquiv n q g v).val =
      (g.val : Mat (q.Extension 2) (n + 2)) *ᵥ v.val := rfl

def fixedLinearHom (n : ℕ) (q : CFSG.PrimePower) :
    relativeRootGroup n q →* (fixedSpace n q ≃ₗ[fixedField q] fixedSpace n q) where
  toFun := fixedLinearEquiv n q
  map_one' := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    rw [fixedLinearEquiv_apply]
    change (1 : Mat (q.Extension 2) (n + 2)) *ᵥ v.val = v.val
    exact Matrix.one_mulVec v.val
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    change (fixedLinearEquiv n q (g * h) v).val =
      (fixedLinearEquiv n q g (fixedLinearEquiv n q h v)).val
    rw [fixedLinearEquiv_apply, fixedLinearEquiv_apply, fixedLinearEquiv_apply]
    change ((g.val : Mat (q.Extension 2) (n + 2)) *
      (h.val : Mat (q.Extension 2) (n + 2))) *ᵥ v.val = _
    exact (Matrix.mulVec_mulVec v.val (g.val : Mat (q.Extension 2) (n + 2)) h.val).symm

theorem fixedLinearHom_apply (n : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup n q) (v : fixedSpace n q) :
    (fixedLinearHom n q g v).val = (g.val : Mat (q.Extension 2) (n + 2)) *ᵥ v.val := by
  change (fixedLinearEquiv n q g v).val = _
  exact fixedLinearEquiv_apply n q g v

theorem fixedLinearHom_preserves_Q (n : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup n q) (v : fixedSpace n q) :
    fixedQuadraticForm n q (fixedLinearHom n q g v) = fixedQuadraticForm n q v := by
  apply Subtype.ext
  rw [fixedQuadraticForm_apply, fixedQuadraticForm_apply, fixedLinearHom_apply]
  exact CFSGTwistedDAllRankHyperbolicPairs.preserves_Q n q g v.val

theorem fixedLinearHom_injective (n : ℕ) (q : CFSG.PrimePower) :
    Function.Injective (fixedLinearHom n q) := by
  intro g h he
  have hl : Matrix.mulVecLin (g.val : Mat (q.Extension 2) (n + 2)) =
      Matrix.mulVecLin (h.val : Mat (q.Extension 2) (n + 2)) := by
    apply LinearMap.ext_on_range (fixedSpace_span n q)
    intro v
    have hv := congrArg
      (fun L : fixedSpace n q ≃ₗ[fixedField q] fixedSpace n q => (L v).val) he
    dsimp only at hv
    rw [fixedLinearHom_apply, fixedLinearHom_apply] at hv
    exact hv
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro i
  exact LinearMap.congr_fun hl (Pi.single i 1)

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedQuadraticAction
