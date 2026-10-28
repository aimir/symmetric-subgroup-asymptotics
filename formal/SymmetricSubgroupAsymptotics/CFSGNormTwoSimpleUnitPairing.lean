import SymmetricSubgroupAsymptotics.CFSGNormTwoSimpleWeightSeparation
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateImageCentralKernel

/-! A root has a unit simple pairing in a connected simply-laced diagram
of rank at least two. This uses the literal positive-definite lattice,
not Weyl transitivity or a root census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoSimpleUnitPairing
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGNormTwoSimpleWeightSeparation
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (hd : ∀ i, A i i = 2) (hs : A.transpose = A)
    (hp : (rationalMatrix A).PosDef)

include hd hs hp

/-- The local geometric statement needs only an actual adjacent node at
any simple root; the connected-diagram theorem below supplies it. -/
theorem exists_simple_unit_pairing_of_neighbors
    (hn : ∀ i : Fin r, ∃ j : Fin r, A i j = -1) (a : Roots A) :
    ∃ i : Fin r, integerPairing A a.val (Pi.single i 1) = 1 ∨
      integerPairing A a.val (Pi.single i 1) = -1 := by
  by_cases ht : ∃ i : Fin r, integerPairing A a.val (Pi.single i 1) = 2
  · obtain ⟨i, hi⟩ := ht
    have he : a = coordinateRoot A hd i :=
      (root_pairing_eq_two_iff A hs hp a (coordinateRoot A hd i)).mp hi
    obtain ⟨j, hj⟩ := hn i
    refine ⟨j, Or.inr ?_⟩
    rw [he]
    change integerPairing A (Pi.single i 1) (Pi.single j 1) = -1
    simpa only [integerPairing, Matrix.toBilin'_single] using hj
  by_cases ht' : ∃ i : Fin r, integerPairing A a.val (Pi.single i 1) = -2
  · obtain ⟨i, hi⟩ := ht'
    have he : a.val = -(coordinateRoot A hd i).val :=
      (root_pairing_eq_neg_two_iff A hs hp a (coordinateRoot A hd i)).mp hi
    obtain ⟨j, hj⟩ := hn i
    refine ⟨j, Or.inl ?_⟩
    rw [he, map_neg]
    change -integerPairing A (Pi.single i 1) (Pi.single j 1) = 1
    norm_num only [integerPairing, Matrix.toBilin'_single, hj]
  by_contra hu
  have hz (i : Fin r) : integerPairing A a.val (Pi.single i 1) = 0 := by
    have hb := root_pairing_bounds A hs hp a (coordinateRoot A hd i)
    change -2 ≤ integerPairing A a.val (Pi.single i 1) ∧
      integerPairing A a.val (Pi.single i 1) ≤ 2 at hb
    have h2 : integerPairing A a.val (Pi.single i 1) ≠ 2 :=
      fun h => ht ⟨i, h⟩
    have hm2 : integerPairing A a.val (Pi.single i 1) ≠ -2 :=
      fun h => ht' ⟨i, h⟩
    have h1 : integerPairing A a.val (Pi.single i 1) ≠ 1 :=
      fun h => hu ⟨i, Or.inl h⟩
    have hm1 : integerPairing A a.val (Pi.single i 1) ≠ -1 :=
      fun h => hu ⟨i, Or.inr h⟩
    omega
  have ha : a.val = 0 := by
    apply label_eq_of_simple_pairings A hs hp
    intro i
    rw [integer_symmetric A hs, hz]
    simp only [map_zero]
  have hh := a.property
  rw [ha, map_zero] at hh
  norm_num at hh

/-- No adjacency premise remains for an actual connected norm-two root
system of rank at least two. The root and Cartan matrix are unchanged. -/
theorem exists_simple_unit_pairing
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    [Nontrivial (Fin r)] (a : Roots A) :
    ∃ i : Fin r, integerPairing A a.val (Pi.single i 1) = 1 ∨
      integerPairing A a.val (Pi.single i 1) = -1 := by
  apply exists_simple_unit_pairing_of_neighbors A hd hs hp (a := a)
  intro i
  obtain ⟨j, _, hj⟩ :=
    CFSGNormTwoCoordinateImageCentralKernel.exists_adjacent_to A hd hs hp ho i
  exact ⟨j, hj⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoSimpleUnitPairing
