import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralRadical

/-! The centre-valued commutator pairing of the ACTUAL signed-Hermitian
radical. Each nonzero vector pairs onto the entire actual central line,
including characteristic two. No subgroup intersection is assumed to be
linear over the larger field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryParameters
variable {K J : Type*} [Field K] [Fintype J]

def hermitianPair (sigma : K ≃+* K) (H : Matrix J J K) (v w : J → K) : K :=
  dotProduct (sigma ∘ v) (H *ᵥ w)

theorem hermitianPair_sigma (sigma : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x) (eps : K) (H : Matrix J J K)
    (hH : H.map sigma = eps • H.transpose) (v w : J → K) :
    sigma (hermitianPair sigma H v w) = eps * hermitianPair sigma H w v := by
  change sigma.toRingHom (dotProduct (sigma ∘ v) (H *ᵥ w)) = _
  rw [RingHom.map_dotProduct]
  have hv : sigma.toRingHom ∘ (sigma ∘ v) = v := by
    funext i
    exact hsigma (v i)
  have hw : sigma.toRingHom ∘ (H *ᵥ w) = H.map sigma *ᵥ (sigma.toRingHom ∘ w) := by
    funext i
    exact RingHom.map_mulVec sigma.toRingHom H w i
  rw [hv, hw, hH, Matrix.smul_mulVec, dotProduct_smul,
    Matrix.dotProduct_transpose_mulVec]
  rfl

theorem hermitianPair_add_left (sigma : K ≃+* K) (H : Matrix J J K)
    (u v w : J → K) :
    hermitianPair sigma H (u + v) w =
      hermitianPair sigma H u w + hermitianPair sigma H v w := by
  have hsum : sigma ∘ (u + v) = (sigma ∘ u) + (sigma ∘ v) := by
    funext i
    exact map_add sigma (u i) (v i)
  change dotProduct (sigma ∘ (u + v)) (H *ᵥ w) = _
  rw [hsum, add_dotProduct]
  rfl

theorem hermitianPair_add_right (sigma : K ≃+* K) (H : Matrix J J K)
    (u v w : J → K) :
    hermitianPair sigma H u (v + w) =
      hermitianPair sigma H u v + hermitianPair sigma H u w := by
  change dotProduct (sigma ∘ u) (H *ᵥ (v + w)) = _
  rw [Matrix.mulVec_add, dotProduct_add]
  rfl

theorem hermitianPair_surjective [DecidableEq J] (sigma : K ≃+* K)
    (H : (Matrix J J K)ˣ) (v : J → K) (hv : v ≠ 0) :
    Function.Surjective (hermitianPair sigma (H : Matrix J J K) v) := by
  have hi : ∃ i, v i ≠ 0 := by
    by_contra hi
    apply hv
    funext i
    by_contra hvi
    exact hi ⟨i, hvi⟩
  obtain ⟨i, hvi⟩ := hi
  have hsi : sigma (v i) ≠ 0 := by
    intro he
    apply hvi
    exact sigma.injective (he.trans (map_zero sigma).symm)
  intro a
  let z : J → K := Pi.single i (a / sigma (v i))
  let w : J → K := (H⁻¹ : (Matrix J J K)ˣ) *ᵥ z
  have hw : (H : Matrix J J K) *ᵥ w = z := by
    dsimp only [w]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  refine ⟨w, ?_⟩
  change dotProduct (sigma ∘ v) ((H : Matrix J J K) *ᵥ w) = a
  rw [hw]
  dsimp only [z]
  rw [dotProduct_single]
  change sigma (v i) * (a / sigma (v i)) = a
  field_simp [hsi]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryParameters

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGSerreOrdinaryTwists CFSGTwistedANaturalMatrices
open CFSGTwistedAUnitaryParameters CFSGTwistedAUnitaryNaturalRadical
open CFSGTwistedAUnitaryUpperArrays

def centralPairParameter (q : CFSG.PrimePower) (s : ℕ)
    (v w : Fin (s + 1) → q.Extension 2) : q.Extension 2 :=
  definingFieldAutomorphism q 2
    (hermitianPair (definingFieldAutomorphism q 2) (middleForm q s) v w) -
      parity q s * hermitianPair (definingFieldAutomorphism q 2) (middleForm q s) v w

theorem centralPairParameter_mem (q : CFSG.PrimePower) (s : ℕ)
    (v w : Fin (s + 1) → q.Extension 2) :
    centralPairParameter q s v w ∈ centralParameters q s := by
  have he : definingFieldAutomorphism q 2 (parity q s) = parity q s := by
    change definingFieldAutomorphism q 2 ((-1) ^ s) = (-1) ^ s
    rw [map_pow, map_neg, map_one]
  have he2 : parity q s * parity q s = 1 := by
    change ((-1 : q.Extension 2) ^ s) * ((-1 : q.Extension 2) ^ s) = 1
    rw [← mul_pow]
    simp
  change definingFieldAutomorphism q 2 (centralPairParameter q s v w) +
    parity q s * centralPairParameter q s v w = 0
  have htwice : definingFieldAutomorphism q 2 (definingFieldAutomorphism q 2
      (hermitianPair (definingFieldAutomorphism q 2) (middleForm q s) v w)) =
      hermitianPair (definingFieldAutomorphism q 2) (middleForm q s) v w :=
    extension_two_pow_twice q _
  dsimp only [centralPairParameter]
  rw [map_sub, map_mul, htwice, he]
  calc
    _ = (1 - parity q s * parity q s) *
      hermitianPair (definingFieldAutomorphism q 2) (middleForm q s) v w := by ring
    _ = 0 := by rw [he2]; ring

def centralPair (q : CFSG.PrimePower) (s : ℕ)
    (v w : Fin (s + 1) → q.Extension 2) : centralParameters q s :=
  ⟨centralPairParameter q s v w, centralPairParameter_mem q s v w⟩

theorem centralPairParameter_add_left (q : CFSG.PrimePower) (s : ℕ)
    (u v w : Fin (s + 1) → q.Extension 2) :
    centralPairParameter q s (u + v) w =
      centralPairParameter q s u w + centralPairParameter q s v w := by
  simp only [centralPairParameter, hermitianPair_add_left, map_add]
  ring

theorem centralPairParameter_add_right (q : CFSG.PrimePower) (s : ℕ)
    (u v w : Fin (s + 1) → q.Extension 2) :
    centralPairParameter q s u (v + w) =
      centralPairParameter q s u v + centralPairParameter q s u w := by
  simp only [centralPairParameter, hermitianPair_add_right, map_add]
  ring

theorem centralPair_alternating (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin (s + 1) → q.Extension 2) : centralPair q s v v = 0 := by
  apply Subtype.ext
  change centralPairParameter q s v v = 0
  unfold centralPairParameter
  rw [hermitianPair_sigma _ (fun x => extension_two_pow_twice q x) _ _
    (middleForm_hermitian q s), sub_self]

theorem firstRow_dotProduct (q : CFSG.PrimePower) (s : ℕ)
    (v w : Fin (s + 1) → q.Extension 2) :
    dotProduct (firstRow q s v) w = -parity q s *
      hermitianPair (definingFieldAutomorphism q 2) (middleForm q s) v w := by
  change dotProduct ((-parity q s) •
    ((definingFieldAutomorphism q 2 ∘ v) ᵥ* middleForm q s)) w = _
  rw [smul_dotProduct, ← Matrix.dotProduct_mulVec]
  rfl

theorem centralPairParameter_eq_commutator (q : CFSG.PrimePower) (s : ℕ)
    (v w : Fin (s + 1) → q.Extension 2) :
    centralPairParameter q s v w =
      dotProduct (firstRow q s v) w - dotProduct (firstRow q s w) v := by
  unfold centralPairParameter
  rw [hermitianPair_sigma _ (fun x => extension_two_pow_twice q x) _ _
    (middleForm_hermitian q s), firstRow_dotProduct, firstRow_dotProduct]
  ring

theorem centralPair_surjective (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin (s + 1) → q.Extension 2) (hv : v ≠ 0) :
    Function.Surjective (centralPair q s v) := by
  intro c
  obtain ⟨t, ht⟩ := exists_signedCentral_commutator_parameter q (parity q s) c.val
    (neg_one_pow_eq_or (q.Extension 2) s) c.property
  obtain ⟨w, hw⟩ := hermitianPair_surjective (definingFieldAutomorphism q 2)
    (-(signedReversalUnit (q.Extension 2) s)) v hv (-t)
  refine ⟨w, ?_⟩
  apply Subtype.ext
  change centralPairParameter q s v w = c.val
  change hermitianPair (definingFieldAutomorphism q 2) (middleForm q s) v w = -t at hw
  change definingFieldAutomorphism q 2
    (hermitianPair (definingFieldAutomorphism q 2) (middleForm q s) v w) -
    parity q s * hermitianPair (definingFieldAutomorphism q 2) (middleForm q s) v w = c.val
  rw [hw, map_neg]
  calc
    _ = parity q s * t - definingFieldAutomorphism q 2 t := by ring
    _ = c.val := ht

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
