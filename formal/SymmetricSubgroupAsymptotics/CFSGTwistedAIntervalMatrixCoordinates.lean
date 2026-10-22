import SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalFiniteSpan
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalCartan

/-! Integral coordinate duality for Cartan and off-diagonal matrix units
in arbitrary natural dimension. Prefix diagonal sums recover the Cartan
coordinates without dividing by the dimension or characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalMatrixCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAIntervalSource
variable (R : Type*) [CommRing R] (r : ℕ)

def prefixDiagonal (M : Mat R r) (i : Fin r) : R :=
  ∑ j : Fin (r + 1), if j.val ≤ i.val then M j j else 0

def matrixVectors : BasisIndex r → Mat R r
  | .inl i => cartan R r i
  | .inr (false, p) => Matrix.single p.val.1 p.val.2 1
  | .inr (true, p) => Matrix.single p.val.2 p.val.1 1

def matrixCoordinates : Mat R r →ₗ[R] (BasisIndex r → R) where
  toFun M i := match i with
    | .inl j => prefixDiagonal R r M j
    | .inr (false, p) => M p.val.1 p.val.2
    | .inr (true, p) => M p.val.2 p.val.1
  map_add' M N := by
    funext i
    rcases i with j | ⟨b, p⟩
    · change (∑ k : Fin (r + 1), if k.val ≤ j.val then (M k k + N k k) else 0) =
        (∑ k : Fin (r + 1), if k.val ≤ j.val then M k k else 0) +
        (∑ k : Fin (r + 1), if k.val ≤ j.val then N k k else 0)
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> simp
    · cases b <;> rfl
  map_smul' a M := by
    funext i
    rcases i with j | ⟨b, p⟩
    · change (∑ k : Fin (r + 1), if k.val ≤ j.val then a • M k k else 0) =
        a • (∑ k : Fin (r + 1), if k.val ≤ j.val then M k k else 0)
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> simp
    · cases b <;> rfl

theorem matrixCoordinates_cartan_apply (M : Mat R r) (i : Fin r) :
    matrixCoordinates R r M (.inl i) = prefixDiagonal R r M i := rfl

theorem matrixCoordinates_positive_apply (M : Mat R r) (p : RootPair r) :
    matrixCoordinates R r M (.inr (false, p)) = M p.val.1 p.val.2 := rfl

theorem matrixCoordinates_negative_apply (M : Mat R r) (p : RootPair r) :
    matrixCoordinates R r M (.inr (true, p)) = M p.val.2 p.val.1 := rfl

theorem prefixDiagonal_single (a b : Fin (r + 1)) (t : R) (i : Fin r) :
    prefixDiagonal R r (Matrix.single a b t) i =
      if a = b ∧ a.val ≤ i.val then t else 0 := by
  unfold prefixDiagonal
  rw [Finset.sum_eq_single a]
  · by_cases hab : a = b
    · subst b; simp [Matrix.single]
    · simp [Matrix.single, hab, Ne.symm hab]
  · intro j _ hja
    simp [Matrix.single, Ne.symm hja]
  · intro ha
    exact False.elim (ha (Finset.mem_univ a))

theorem prefixDiagonal_cartan (j i : Fin r) :
    prefixDiagonal R r (cartan R r j) i = if j = i then 1 else 0 := by
  rw [cartan_eq]
  have hs (M N : Mat R r) : prefixDiagonal R r (M - N) i =
      prefixDiagonal R r M i - prefixDiagonal R r N i := by
    unfold prefixDiagonal
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp
  rw [hs]
  rw [prefixDiagonal_single, prefixDiagonal_single]
  simp only [true_and, Fin.val_castSucc, Fin.val_succ]
  by_cases hji : j = i
  · subst i; simp
  · have hv : j.val ≠ i.val := fun he => hji (Fin.ext he)
    by_cases hlt : j.val < i.val
    · simp [hji, show j.val ≤ i.val by omega, show j.val + 1 ≤ i.val by omega]
    · simp [hji, show ¬j.val ≤ i.val by omega, show ¬j.val + 1 ≤ i.val by omega]

theorem cartan_offDiagonal (j : Fin r) (a b : Fin (r + 1)) (hab : a ≠ b) :
    cartan R r j a b = 0 := by
  rw [cartan_eq_diagonal, Matrix.diagonal_apply_ne _ hab]

theorem pair_eq_iff (p q : RootPair r) :
    p = q ↔ p.val.1 = q.val.1 ∧ p.val.2 = q.val.2 := by
  constructor
  · intro h; subst q; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩; exact Subtype.ext (Prod.ext h1 h2)

theorem pair_cross_ne (p q : RootPair r) :
    ¬ (p.val.1 = q.val.2 ∧ p.val.2 = q.val.1) := by
  rintro ⟨h1, h2⟩
  have hp := p.property
  have hq := q.property
  rw [h1, h2] at hp
  exact (not_lt_of_ge hp.le) hq

theorem coordinates_vector (j : BasisIndex r) :
    matrixCoordinates R r (matrixVectors R r j) = Pi.single j 1 := by
  funext i
  rcases j with j | ⟨b, p⟩
  · rcases i with i | ⟨b, p⟩
    · change prefixDiagonal R r (cartan R r j) i = _
      rw [prefixDiagonal_cartan]
      simp only [Pi.single_apply, Sum.inl.injEq, eq_comm]
    · have hp : p.val.1 ≠ p.val.2 := ne_of_lt p.property
      cases b
      · simp only [matrixVectors, matrixCoordinates_positive_apply,
          cartan_offDiagonal R r j _ _ hp, Pi.single_apply, Sum.inr_ne_inl, if_false]
      · simp only [matrixVectors, matrixCoordinates_negative_apply,
          cartan_offDiagonal R r j _ _ hp.symm, Pi.single_apply, Sum.inr_ne_inl, if_false]
  · rcases i with i | ⟨c, q⟩
    · have hp : p.val.1 ≠ p.val.2 := ne_of_lt p.property
      cases b <;> simp only [matrixVectors, matrixCoordinates_cartan_apply,
        prefixDiagonal_single, hp, hp.symm, false_and, if_false,
        Pi.single_apply, Sum.inl_ne_inr]
    · have hsame := pair_eq_iff r p q
      have hcross := pair_cross_ne r p q
      cases b <;> cases c <;>
        simp only [matrixVectors, matrixCoordinates_positive_apply,
          matrixCoordinates_negative_apply, Matrix.single_apply,
          Pi.single_apply, Sum.inr.injEq, Prod.mk.injEq, Bool.false_eq_true,
          Bool.true_eq_false, true_and, false_and, if_false]
      · simp only [← hsame, eq_comm]
      · exact if_neg hcross
      · have hc : ¬ (p.val.2 = q.val.1 ∧ p.val.1 = q.val.2) :=
          fun h => hcross ⟨h.2, h.1⟩
        exact if_neg hc
      · simp only [and_comm, ← hsame, eq_comm]

def matrixCombination : (BasisIndex r → R) →ₗ[R] Mat R r :=
  Fintype.linearCombination R (matrixVectors R r)

theorem coordinates_combination (a : BasisIndex r → R) :
    matrixCoordinates R r (matrixCombination R r a) = a := by
  change matrixCoordinates R r (∑ i, a i • matrixVectors R r i) = a
  rw [map_sum]
  simp only [map_smul, coordinates_vector]
  funext j
  simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul]

theorem matrixCombination_injective : Function.Injective (matrixCombination R r) := by
  intro a b h
  have hh := congrArg (matrixCoordinates R r) h
  simpa only [coordinates_combination] using hh

theorem map_matrixVectors {S : Type*} [CommRing S] (f : R →+* S) (j : BasisIndex r) :
    f.mapMatrix (matrixVectors R r j) = matrixVectors S r j := by
  rcases j with j | ⟨b, p⟩
  · exact map_cartan R r f j
  · cases b
    all_goals
      change (Matrix.single _ _ (1 : R)).map f = Matrix.single _ _ (1 : S)
      simp only [Matrix.map_single, map_one]

end SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalMatrixCoordinates
