import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationSLChain
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSignedPermutation

/-! Genuine simultaneous signed point permutations in B, obtained from
its proved SL-chain embedding. Both paired coordinates carry the same
sign, and the original middle coordinate remains fixed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationSignedPermutation
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationSLChain
open CFSGTypeAMonomialMatrices
variable (K : Type) [Field K]

def naturalPermutation (r : ℕ) (σ : Equiv.Perm (Fin r)) : Equiv.Perm (Index r) :=
  Equiv.sumCongr (Equiv.sumCongr σ σ) (Equiv.refl Unit)

def naturalWeight (r : ℕ) (b : Fin r) (σ : Equiv.Perm (Fin r)) : Index r → K :=
  Sum.elim
    (Sum.elim (CFSGOrthogonalDGenerationSignedPermutation.weight K b σ)
      (CFSGOrthogonalDGenerationSignedPermutation.weight K b σ))
    (fun _ => 1)

theorem naturalWeight_mul_self (r : ℕ) (b : Fin r) (σ : Equiv.Perm (Fin r))
    (x : Index r) : naturalWeight K r b σ x * naturalWeight K r b σ x = 1 := by
  rcases x with ((i | i) | ⟨⟩)
  · exact CFSGOrthogonalDGenerationSignedPermutation.weight_mul_self K b σ i
  · exact CFSGOrthogonalDGenerationSignedPermutation.weight_mul_self K b σ i
  · simp [naturalWeight]

theorem naturalWeight_ne_zero (r : ℕ) (b : Fin r) (σ : Equiv.Perm (Fin r))
    (x : Index r) : naturalWeight K r b σ x ≠ 0 := by
  intro he
  have hh := naturalWeight_mul_self K r b σ x
  rw [he, zero_mul] at hh
  exact zero_ne_one hh

def signedPermutationElement (r : ℕ) (b : Fin r) (σ : Equiv.Perm (Fin r)) :
    elementaryRootGroup K r :=
  doubleIntoElementary K r (CFSGTypeAMonomialMatrices.signedPermutation (F := K) b σ)

theorem signedPermutationElement_val (r : ℕ) (b : Fin r) (σ : Equiv.Perm (Fin r)) :
    ((signedPermutationElement K r b σ).val : Mat K r) =
      monomial (naturalPermutation r σ) (naturalWeight K r b σ) := by
  change CFSGMatrixIdentityExtension.extend K (Fin r ⊕ Fin r) Unit
    ((CFSGOrthogonalDGenerationSignedPermutation.signedPermutationElement K r b σ).val :
      CFSGOrthogonalDSerreMatrices.Mat K r) = _
  rw [CFSGOrthogonalDGenerationSignedPermutation.signedPermutationElement_coe]
  ext x y
  rcases x with ((x | x) | ⟨⟩) <;> rcases y with ((y | y) | ⟨⟩) <;>
    simp [CFSGMatrixIdentityExtension.extend, Matrix.fromBlocks, monomial_apply,
      naturalPermutation, naturalWeight]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationSignedPermutation
