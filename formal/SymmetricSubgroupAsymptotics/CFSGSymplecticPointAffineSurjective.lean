import SymmetricSubgroupAsymptotics.CFSGSymplecticPointAffineHom
import SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergWords
import SymmetricSubgroupAsymptotics.CFSGSymplecticUniformTail

/-! Actual elementary shear words supply every translation, and the
actual first-pair tail supplies the linear factor. Thus the literal
point-to-affine homomorphism is onto. No split structure for the point
stabilizer, and no characteristic assumption, is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticPointAffineSurjective
open CFSGSymplecticSerreMatrices CFSGSymplecticStabilizerCoordinates
open CFSGSymplecticTransvectionGeometry CFSGSymplecticHeisenbergWords
open CFSGSymplecticHeisenbergOperators CFSGSymplecticUniformTail
open CFSGSymplecticPointTailCoordinates CFSGSymplecticPointAffineCoordinates
open CFSGSymplecticPointAffineHom LinearSemidirectCommutingFibres
variable (K : Type) [Field K]

private theorem first_tail_pairing (r : ℕ) (v : Index r → K) :
    pairing (r+1) (Pi.single (Sum.inl 0) 1) (tailExtend r v) = 0 := by
  rw [pairing_pos_basis_left, tailExtend_neg_zero]

def translationElement (r : ℕ) (hr : 0 < r) (v : Index r → K) :
    pointStabilizer K r :=
  ⟨shearElement K r hr (Pi.single (Sum.inl 0) 1) (tailExtend r v) 0, by
    change ((shearElement K r hr _ _ 0).val : Mat K (r+1)) *ᵥ _ = _
    rw [shearElement_apply, shear_apply _ _ _ _ _ (first_tail_pairing K r v)]
    simp only [pairing_pos_basis, tailExtend_neg_zero, neg_zero, pairing_self,
      zero_smul, zero_mul, add_zero]⟩

theorem translationElement_apply (r : ℕ) (hr : 0 < r)
    (v : Index r → K) (x : Index (r+1) → K) :
    ((translationElement K r hr v).val.val : Mat K (r+1)) *ᵥ x =
      x + pairing (r+1) (tailExtend r v) x • Pi.single (Sum.inl 0) 1 +
        pairing (r+1) (Pi.single (Sum.inl 0) 1) x • tailExtend r v := by
  change ((shearElement K r hr _ _ 0).val : Mat K (r+1)) *ᵥ x = _
  rw [shearElement_apply, shear_apply _ _ _ _ _ (first_tail_pairing K r v)]
  rw [zero_mul, zero_smul, add_zero]

theorem translationElement_tail (r : ℕ) (hr : 0 < r) (v : Index r → K) :
    pointTailHom K r (translationElement K r hr v) = 1 := by
  apply Subtype.ext
  apply Units.ext
  have hm (w : Index r → K) :
      tailMatrix r ((translationElement K r hr v).val.val : Mat K (r+1)) *ᵥ w = w := by
    rw [tailMatrix_mulVec]
    funext i
    change (((translationElement K r hr v).val.val : Mat K (r+1)) *ᵥ
      tailExtend r w) (tailIndex r i) = w i
    rw [translationElement_apply, first_tail_pairing K r w]
    cases i <;> simp [tailIndex, tailExtend]
  ext i j
  have he := congrFun (hm (Pi.single j 1)) i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.one_apply,
    Pi.single_apply] using he

theorem translationElement_partner (r : ℕ) (hr : 0 < r) (v : Index r → K) :
    partnerColumn K r ((translationElement K r hr v).val.val : Mat K (r+1)) = v := by
  have he := translationElement_apply K r hr v (Pi.single (Sum.inr 0) 1)
  rw [pairing_neg_basis, tailExtend_pos_zero, pairing_pos_basis_left] at he
  simp only [Pi.single_eq_same, zero_smul, add_zero, one_smul] at he
  funext i
  have hi := congrFun he (tailIndex r i)
  cases i <;> simpa [partnerColumn, Matrix.mulVec_single_one, Matrix.col_apply,
    tailIndex, Pi.single_apply] using hi

theorem pointAffine_translation (r : ℕ) (hr : 0 < r) (v : Index r → K) :
    pointAffineHom K r (translationElement K r hr v) =
      SemidirectProduct.inl (Multiplicative.ofAdd v) := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    exact translationElement_partner K r hr v
  · exact translationElement_tail K r hr v

private def tailElement (r : ℕ) (A : elementaryRootGroup K r) : pointStabilizer K r :=
  ⟨tailHom K r A,(tailHom_fixes_firstPair K r A).1⟩

theorem pointAffine_tail (r : ℕ) (A : elementaryRootGroup K r) :
    pointAffineHom K r (tailElement K r A) = SemidirectProduct.inr A := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    have he := fixed_basis_column (r+1)
      ((tailHom K r A).val : Mat K (r+1)) (Sum.inr 0)
      (tailHom_fixes_firstPair K r A).2 (tailIndex r i)
    cases i <;> simpa [partnerColumn, tailElement, tailIndex, Pi.single_apply] using he
  · apply Subtype.ext
    apply Units.ext
    exact tailHom_tailMatrix K r A

theorem pointAffineHom_surjective (r : ℕ) (hr : 0 < r) :
    Function.Surjective (pointAffineHom K r) := by
  intro x
  refine ⟨translationElement K r hr x.left.toAdd * tailElement K r x.right, ?_⟩
  rw [map_mul, pointAffine_translation, pointAffine_tail]
  exact SemidirectProduct.inl_left_mul_inr_right x

end SymmetricSubgroupAsymptotics.CFSGSymplecticPointAffineSurjective
