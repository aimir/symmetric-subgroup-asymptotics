import SymmetricSubgroupAsymptotics.CFSGSymplecticNaturalBilinearClassGeometry

/-! Append one literal paired coordinate to two finite coordinate
strings. The actual natural symplectic pairing splits into the original
strings and this final pair. This is a linear coordinate calculation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.SymplecticLastPairCoordinates
open CFSGSymplecticSerreMatrices CFSGSymplecticNaturalBilinearClassGeometry
variable (K : Type) [Field K]

def appendEquiv (n : ℕ) :
    ((Fin n → K) × ((Fin n → K) × (K × K))) ≃ₗ[K] (Index (n+1) → K) where
  toFun x
    | Sum.inl i => Fin.lastCases x.2.2.1 x.1 i
    | Sum.inr i => Fin.lastCases x.2.2.2 x.2.1 i
  invFun v := (fun i => v (Sum.inl i.castSucc),
    (fun i => v (Sum.inr i.castSucc), (v (Sum.inl (Fin.last n)), v (Sum.inr (Fin.last n)))))
  left_inv x := by
    apply Prod.ext
    · funext i
      simp
    · apply Prod.ext
      · funext i
        simp
      · apply Prod.ext <;> simp
  right_inv v := by
    funext i
    cases i with
    | inl i => rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl <;> simp
    | inr i => rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl <;> simp
  map_add' x y := by
    funext i
    cases i with
    | inl i => rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl <;> simp
    | inr i => rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl <;> simp
  map_smul' a x := by
    funext i
    cases i with
    | inl i => rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl <;> simp
    | inr i => rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl <;> simp

theorem pairing_append (n : ℕ)
    (x y : (Fin n → K) × ((Fin n → K) × (K × K))) :
    naturalPairing K (n+1) (appendEquiv K n x) (appendEquiv K n y) =
      (∑ i : Fin n, (x.1 i*y.2.1 i-x.2.1 i*y.1 i)) +
        (x.2.2.1*y.2.2.2-x.2.2.2*y.2.2.1) := by
  change (∑ i : Fin (n+1),
    (appendEquiv K n x (Sum.inl i) * appendEquiv K n y (Sum.inr i) -
      appendEquiv K n x (Sum.inr i) * appendEquiv K n y (Sum.inl i))) = _
  rw [Fin.sum_univ_castSucc]
  simp [appendEquiv]

end SymmetricSubgroupAsymptotics.SymplecticLastPairCoordinates
