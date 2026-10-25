import SymmetricSubgroupAsymptotics.PuncturedAnnihilatorScalarWordIndex

/-! A proper prime-field subspace preserved by an actual subgroup of a
scalar-rich action has cardinality at most the SAME subgroup index.
The proof uses its punctured dual annihilator; arbitrary action elements
need not be linear over the larger field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarInvariantSubspaceCardIndex

theorem card_le_index_of_scalar_words
    {F K T : Type*} [Field F] [Field K] [Algebra F K] [Group T]
    [Finite F] [Finite K] [Finite T] [Module.Finite F K]
    (ρ : T →* K ≃ₗ[F] K)
    (hscalar : ∀ a : Kˣ, ∃ t : T, ∀ x : K, ρ t x=(a : K)*x)
    (L : Subgroup T) (C : Submodule F K)
    (hC : ∀ t ∈ L, ∀ x ∈ C, ρ t x ∈ C) (hne : C ≠ ⊤) :
    Nat.card C ≤ L.index := by
  letI : Finite (K ⧸ C) := Finite.of_surjective C.mkQ C.mkQ_surjective
  obtain ⟨z,hz⟩ : ∃ z : K, z ∉ C := by
    by_contra h
    apply hne
    apply top_unique
    intro z _
    exact not_not.mp (not_exists.mp h z)
  obtain ⟨f,hf⟩ := InvariantAnnihilatorOrbitIndex.exists_annihilator_nonzero_on C z hz
  have hf0 : f.val ≠ 0 := by
    intro h
    exact hf (by rw [h]; rfl)
  have ho : Nat.card K-1 ≤ (Nat.card (K ⧸ C)-1)*L.index :=
    (ScalarWordDualAnnihilatorOrbitIndex.dual_orbit_card_ge ρ hscalar f.val hf0).trans
      (PuncturedAnnihilatorScalarWordIndex.dual_orbit_card_le_punctured_quotient_card_mul_index
        ρ L C hC f hf0)
  have hcard : Nat.card K=Nat.card (K ⧸ C)*Nat.card C := by
    rw [Submodule.card_eq_card_quotient_mul_card C]
    exact Nat.mul_comm _ _
  have hsub : (Nat.card (K ⧸ C)-1)*Nat.card C ≤ Nat.card K-1 := by
    have hQpos : 0 < Nat.card (K ⧸ C) := Nat.card_pos
    have hCpos : 0 < Nat.card C := Nat.card_pos
    have he : (Nat.card (K ⧸ C)-1)*Nat.card C+Nat.card C=Nat.card K := by
      calc
        _ = (Nat.card (K ⧸ C)-1+1)*Nat.card C := by ring
        _ = Nat.card (K ⧸ C)*Nat.card C :=
          congrArg (fun n : ℕ => n*Nat.card C) (by omega)
        _ = Nat.card K := hcard.symm
    omega
  have hh : (Nat.card K-1)*Nat.card C ≤ (Nat.card K-1)*L.index := by
    calc
      _ ≤ ((Nat.card (K ⧸ C)-1)*L.index)*Nat.card C := Nat.mul_le_mul_right _ ho
      _ = ((Nat.card (K ⧸ C)-1)*Nat.card C)*L.index := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ hsub
  exact Nat.le_of_mul_le_mul_left hh
    (by have hq : 1 < Nat.card K := Finite.one_lt_card; omega)

theorem card_le_index_of_surjective_scalars
    {F K T : Type*} [Field F] [Field K] [Algebra F K] [Group T]
    [Finite F] [Finite K] [Finite T] [Module.Finite F K]
    (s : T →* Kˣ) (hs : Function.Surjective s)
    (L : Subgroup T) (C : Submodule F K)
    (hC : ∀ t ∈ L, ∀ x ∈ C,
      ScalarDualAnnihilatorOrbitIndex.scalarAction (F := F) s t x ∈ C) (hne : C ≠ ⊤) :
    Nat.card C ≤ L.index :=
  card_le_index_of_scalar_words (ScalarDualAnnihilatorOrbitIndex.scalarAction s)
    (fun a => by obtain ⟨t,ht⟩ := hs a; exact ⟨t,fun x => by change (s t : K)*x=(a : K)*x; rw [ht]⟩)
    L C hC hne

end SymmetricSubgroupAsymptotics.ScalarInvariantSubspaceCardIndex
