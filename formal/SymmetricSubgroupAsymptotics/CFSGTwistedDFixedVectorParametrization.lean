import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorCardinality

/-! Exact coordinate parametrization of the defining-fixed carrier.
The final negative coordinate is the Frobenius of the final positive
coordinate; all untouched coordinates belong to the actual fixed field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorParametrization
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDFixedVectorCardinality CFSGTwistedDNaturalQuadraticTwist
open CFSGTwistedA2FixedField CFSGSerreOrdinaryTwists CFSGTwistedDNaturalFork

def Parameters (n : ℕ) (q : CFSG.PrimePower) :=
  (Fin (n + 1) → fixedField q) ×
    ((Fin (n + 1) → fixedField q) × q.Extension 2)

def fromParameters (n : ℕ) (q : CFSG.PrimePower) (x : Parameters n q) :
    Index (n + 2) → q.Extension 2
  | Sum.inl i => Fin.lastCases x.2.2 (fun j => (x.1 j : q.Extension 2)) i
  | Sum.inr i => Fin.lastCases (definingFieldAutomorphism q 2 x.2.2)
      (fun j => (x.2.1 j : q.Extension 2)) i

theorem fromParameters_fixed (n : ℕ) (q : CFSG.PrimePower) (x : Parameters n q) :
    vectorTwist (q.Extension 2) n (definingFieldAutomorphism q 2) (fromParameters n q x) =
      fromParameters n q x := by
  funext y
  cases y with
  | inl i =>
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · change definingFieldAutomorphism q 2
        (fromParameters n q x (CFSGOrthogonalDGenerationForkTorus.flip n (Sum.inl j.castSucc))) = _
      have hn : j.castSucc ≠ last n := Fin.castSucc_ne_last j
      rw [flip_pos, if_neg hn]
      simpa only [fromParameters, Fin.lastCases_castSucc] using (x.1 j).property
    · change definingFieldAutomorphism q 2
        (fromParameters n q x (CFSGOrthogonalDGenerationForkTorus.flip n (Sum.inl (last n)))) = _
      rw [flip_pos, if_pos rfl]
      simpa only [fromParameters, last, Fin.lastCases_last] using
        CFSGTwistedANaturalMatrices.extension_two_pow_twice q x.2.2
  | inr i =>
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · change definingFieldAutomorphism q 2
        (fromParameters n q x (CFSGOrthogonalDGenerationForkTorus.flip n (Sum.inr j.castSucc))) = _
      have hn : j.castSucc ≠ last n := Fin.castSucc_ne_last j
      rw [flip_neg, if_neg hn]
      simpa only [fromParameters, Fin.lastCases_castSucc] using (x.2.1 j).property
    · change definingFieldAutomorphism q 2
        (fromParameters n q x (CFSGOrthogonalDGenerationForkTorus.flip n (Sum.inr (last n)))) = _
      rw [flip_neg, if_pos rfl]
      simp only [fromParameters, last, Fin.lastCases_last]

def parameterVector (n : ℕ) (q : CFSG.PrimePower) (x : Parameters n q) : fixedVectors n q :=
  ⟨fromParameters n q x, fromParameters_fixed n q x⟩

theorem encoding_parameterVector (n : ℕ) (q : CFSG.PrimePower) (x : Parameters n q) :
    coordinateEncoding n q (parameterVector n q x) = x := by
  apply Prod.ext
  · funext j
    apply Subtype.ext
    simp only [coordinateEncoding, parameterVector, fromParameters, Fin.lastCases_castSucc]
  · apply Prod.ext
    · funext j
      apply Subtype.ext
      simp only [coordinateEncoding, parameterVector, fromParameters, Fin.lastCases_castSucc]
    · simp only [coordinateEncoding, parameterVector, fromParameters, last, Fin.lastCases_last]

def parameterEquiv (n : ℕ) (q : CFSG.PrimePower) : fixedVectors n q ≃ Parameters n q where
  toFun := coordinateEncoding n q
  invFun := parameterVector n q
  left_inv v := (coordinateEncoding_injective n q) (encoding_parameterVector n q _)
  right_inv := encoding_parameterVector n q

theorem fixedVectors_card (n : ℕ) (q : CFSG.PrimePower) :
    Nat.card (fixedVectors n q) = q.order ^ (2 * (n + 2)) := by
  rw [Nat.card_congr (parameterEquiv n q)]
  simp only [Parameters, Nat.card_prod, Nat.card_fun, Nat.card_fin, fixedField_card,
    CFSGTwistedANaturalMatrices.extension_two_card]
  rw [← pow_add, ← pow_add]
  congr 1
  omega

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorParametrization
