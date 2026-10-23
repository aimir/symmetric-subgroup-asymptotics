import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHeisenbergPairing

/-! Literal sesquilinear pairing transport. No involution, positivity,
finite field, or nondegeneracy premise is needed for these identities. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryParameters
variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]

theorem hermitianPair_isometry (sigma : K ≃+* K) (H A : Matrix I I K)
    (hA : (A.map sigma).transpose * H * A = H) (v w : I → K) :
    hermitianPair sigma H (A *ᵥ v) (A *ᵥ w) = hermitianPair sigma H v w := by
  have hmap : sigma ∘ (A *ᵥ v) = A.map sigma *ᵥ (sigma ∘ v) := by
    funext i
    exact RingHom.map_mulVec sigma.toRingHom A v i
  change dotProduct (sigma ∘ (A *ᵥ v)) (H *ᵥ (A *ᵥ w)) =
    dotProduct (sigma ∘ v) (H *ᵥ w)
  rw [hmap]
  calc
    _ = dotProduct (sigma ∘ v) ((A.map sigma).transpose *ᵥ (H *ᵥ (A *ᵥ w))) := by
      rw [Matrix.dotProduct_mulVec (sigma ∘ v) (A.map sigma).transpose
        (H *ᵥ (A *ᵥ w)), Matrix.vecMul_transpose]
    _ = dotProduct (sigma ∘ v) (((A.map sigma).transpose * H * A) *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = _ := by rw [hA]

theorem hermitianPair_smul (sigma : K ≃+* K) (H : Matrix I I K)
    (a b : K) (v w : I → K) :
    hermitianPair sigma H (a • v) (b • w) =
      sigma a * b * hermitianPair sigma H v w := by
  have hmap : sigma ∘ (a • v) = sigma a • (sigma ∘ v) := by
    funext i
    exact map_mul sigma a (v i)
  change dotProduct (sigma ∘ (a • v)) (H *ᵥ (b • w)) = _
  rw [hmap, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  change sigma a * (b * hermitianPair sigma H v w) = _
  exact (mul_assoc _ _ _).symm

theorem hermitianPair_reindex (sigma : K ≃+* K) (e : I ≃ J)
    (H : Matrix I I K) (v w : J → K) :
    hermitianPair sigma (Matrix.reindex e e H) v w =
      hermitianPair sigma H (v ∘ e) (w ∘ e) := by
  change dotProduct (sigma ∘ v) (H.submatrix e.symm e.symm *ᵥ w) =
    dotProduct (sigma ∘ (v ∘ e)) (H *ᵥ (w ∘ e))
  rw [Matrix.submatrix_mulVec_equiv, dotProduct_comp_equiv_symm]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryParameters
