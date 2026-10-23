import SymmetricSubgroupAsymptotics.CFSGHermitianPairTransport

/-! Exact matrix pullback and coefficient recovery for the literal
sigma(v) dot H*w pairing. These identities hold in characteristic two
and do not require a Hermitian normalization or group recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGHermitianMatrixPullback
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

theorem pullback (sigma : K ≃+* K) (H A : Matrix I I K) (v w : I → K) :
    hermitianPair sigma H (A *ᵥ v) (A *ᵥ w) =
      hermitianPair sigma ((A.map sigma).transpose * H * A) v w := by
  have hmap : sigma ∘ (A *ᵥ v) = A.map sigma *ᵥ (sigma ∘ v) := by
    funext i
    exact RingHom.map_mulVec sigma.toRingHom A v i
  change dotProduct (sigma ∘ (A *ᵥ v)) (H *ᵥ (A *ᵥ w)) = _
  rw [hmap]
  calc
    _ = dotProduct (sigma ∘ v) ((A.map sigma).transpose *ᵥ (H *ᵥ (A *ᵥ w))) := by
      rw [Matrix.dotProduct_mulVec (sigma ∘ v) (A.map sigma).transpose
        (H *ᵥ (A *ᵥ w)), Matrix.vecMul_transpose]
    _ = _ := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]; rfl

theorem basis_pair (sigma : K ≃+* K) (H : Matrix I I K) (i j : I) :
    hermitianPair sigma H (Pi.single i 1) (Pi.single j 1) = H i j := by
  have hm : sigma ∘ Pi.single i (1 : K) = Pi.single i 1 := by
    funext k
    by_cases hk : k = i <;> simp [Function.comp_def, Pi.single_apply, hk]
  change dotProduct (sigma ∘ Pi.single i 1) (H *ᵥ Pi.single j 1) = _
  rw [hm, single_dotProduct, one_mul, Matrix.mulVec_single_one]
  rfl

theorem form_eq_iff_matrix_eq (sigma : K ≃+* K) (H G : Matrix I I K) :
    (∀ v w, hermitianPair sigma H v w = hermitianPair sigma G v w) ↔ H = G := by
  constructor
  · intro he
    ext i j
    simpa only [basis_pair] using he (Pi.single i 1) (Pi.single j 1)
  · rintro rfl v w
    rfl

theorem scalar_form (sigma : K ≃+* K) (H : Matrix I I K) (c : K) (v w : I → K) :
    hermitianPair sigma (c • H) v w = c * hermitianPair sigma H v w := by
  change dotProduct (sigma ∘ v) ((c • H) *ᵥ w) = _
  rw [Matrix.smul_mulVec, dotProduct_smul]
  rfl

theorem similitude_matrix_iff (sigma : K ≃+* K) (H A : Matrix I I K) (c : K) :
    (∀ v w, hermitianPair sigma H (A *ᵥ v) (A *ᵥ w) = c * hermitianPair sigma H v w) ↔
      (A.map sigma).transpose * H * A = c • H := by
  constructor
  · intro he
    apply (form_eq_iff_matrix_eq sigma _ _).mp
    intro v w
    rw [← pullback, scalar_form]
    exact he v w
  · intro hm v w
    rw [pullback, hm, scalar_form]

end SymmetricSubgroupAsymptotics.CFSGHermitianMatrixPullback
