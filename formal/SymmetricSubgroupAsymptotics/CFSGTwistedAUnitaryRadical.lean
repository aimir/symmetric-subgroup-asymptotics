import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperIsometry

/-! Genuine signed-Hermitian radical isometries, including q=2.
Every scalar cross-term equation from the raw array calculation is now
proved from the actual Frobenius involution and trace parameters. The
middle form is arbitrary of the stated signed-Hermitian type. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays
open CFSGTwistedAUnitaryParameters CFSGSerreOrdinaryTwists
open CFSGTwistedANaturalMatrices
variable {K J : Type*} [Field K] [Fintype J] [DecidableEq J]

def radicalRow (sigma : K ≃+* K) (eps : K) (H : Matrix J J K) (v : J → K) : J → K :=
  fun i => -eps * (((sigma ∘ v) ᵥ* H) i)

theorem radicalRow_left (sigma : K ≃+* K) (hsigma : ∀ a, sigma (sigma a) = a)
    (eps : K) (heps : eps = 1 ∨ eps = -1) (H : Matrix J J K)
    (hH : H.map sigma = eps • H.transpose) (v : J → K) (i : J) :
    sigma (radicalRow sigma eps H v i) + (H *ᵥ v) i = 0 := by
  have hse : sigma eps = eps := by rcases heps with rfl | rfl <;> simp
  have he2 : eps * eps = 1 := by rcases heps with rfl | rfl <;> ring
  have hv : sigma.toRingHom ∘ (sigma ∘ v) = v := by
    funext j
    exact hsigma (v j)
  have hm : sigma (((sigma ∘ v) ᵥ* H) i) = eps * (H *ᵥ v) i := by
    have hx := RingHom.map_vecMul sigma.toRingHom H (sigma ∘ v) i
    rw [hv] at hx
    change sigma (((sigma ∘ v) ᵥ* H) i) = (v ᵥ* H.map sigma) i at hx
    rw [hH, Matrix.vecMul_smul, Matrix.vecMul_transpose] at hx
    exact hx
  change sigma (-eps * (((sigma ∘ v) ᵥ* H) i)) + (H *ᵥ v) i = 0
  rw [map_mul, map_neg, hse, hm]
  calc
    -eps * (eps * (H *ᵥ v) i) + (H *ᵥ v) i = (1 - eps * eps) * (H *ᵥ v) i := by ring
    _ = 0 := by rw [he2]; ring

omit [DecidableEq J] in
theorem radicalRow_right (sigma : K ≃+* K) (eps : K) (heps : eps = 1 ∨ eps = -1)
    (H : Matrix J J K) (v : J → K) (i : J) :
    ((sigma ∘ v) ᵥ* H) i + eps * radicalRow sigma eps H v i = 0 := by
  have he2 : eps * eps = 1 := by rcases heps with rfl | rfl <;> ring
  change ((sigma ∘ v) ᵥ* H) i + eps * (-eps * (((sigma ∘ v) ᵥ* H) i)) = 0
  calc
    _ = (1 - eps * eps) * (((sigma ∘ v) ᵥ* H) i) := by ring
    _ = 0 := by rw [he2]; ring

theorem radicalArray_isometry (sigma : K ≃+* K) (hsigma : ∀ a, sigma (sigma a) = a)
    (eps : K) (heps : eps = 1 ∨ eps = -1) (H : Matrix J J K)
    (hH : H.map sigma = eps • H.transpose) (v : J → K) (b : K)
    (hb : sigma b + eps * b = -hermitianNorm sigma H v) :
    ((upperArray (radicalRow sigma eps H v) v b).map sigma).transpose * blockForm eps H *
      upperArray (radicalRow sigma eps H v) v b = blockForm eps H := by
  apply upperArray_isometry sigma.toRingHom eps H (radicalRow sigma eps H v) v b
    (radicalRow_left sigma hsigma eps heps H hH v)
    (radicalRow_right sigma eps heps H v)
  change sigma b + hermitianNorm sigma H v + eps * b = 0
  calc
    _ = hermitianNorm sigma H v + (sigma b + eps * b) := by ring
    _ = 0 := by rw [hb]; ring

theorem exists_radicalArray_isometry (q : CFSG.PrimePower) (eps : q.Extension 2)
    (heps : eps = 1 ∨ eps = -1) (H : Matrix J J (q.Extension 2))
    (hH : H.map (definingFieldAutomorphism q 2) = eps • H.transpose)
    (v : J → q.Extension 2) :
    ∃ b : q.Extension 2,
      ((upperArray (radicalRow (definingFieldAutomorphism q 2) eps H v) v b).map
        (definingFieldAutomorphism q 2)).transpose * blockForm eps H *
        upperArray (radicalRow (definingFieldAutomorphism q 2) eps H v) v b = blockForm eps H := by
  obtain ⟨b, hb⟩ := exists_block_parameter q eps heps H hH v
  exact ⟨b, radicalArray_isometry _ (fun a => extension_two_pow_twice q a)
    eps heps H hH v b hb⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays
