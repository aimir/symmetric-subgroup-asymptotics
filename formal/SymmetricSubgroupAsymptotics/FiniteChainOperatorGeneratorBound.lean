import SymmetricSubgroupAsymptotics.AlgebraOperatorLeadingGeneratorBound

/-! A finite chain certificate needs only genuine successor operators.
The abstract induction composes them on the same original module. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {k A M : Type} [Field k] [Ring A] [Algebra k A]
    [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    {n d w : ℕ}

theorem algebra_generating_finset_le_of_chain_successors
    (hd : ModuleGeneratedBy A M d) (C : M →ₗ[k] (Fin n → k))
    (hC : Function.Injective C) (a0 : Fin n)
    (colour : Fin n → Fin w) (rank : Fin n → ℕ) (next : Fin n → Fin n)
    (hlabels : ∀ a b, colour a = colour b → rank a = rank b → a = b)
    (hadvance : ∀ a b, colour a = colour b → rank a < rank b →
      colour (next a) = colour a ∧ rank (next a) = rank a + 1)
    (hnext : ∀ v a, FiniteRowLeadingWeight.HasLeading (C v) a →
      ∃ r : A, FiniteRowLeadingWeight.HasLeading (C (r • v)) (next a)) :
    ∃ S : Finset M, Submodule.span A (S : Set M) = ⊤ ∧ S.card ≤ w := by
  let rel : Fin n → Fin n → Prop := fun a b => colour a = colour b ∧ rank a ≤ rank b
  have hwidth (s : Finset (Fin n)) (hs : IsAntichain rel (s : Set (Fin n))) : s.card ≤ w := by
    classical
    have hinj : Set.InjOn colour (s : Set (Fin n)) := by
      intro a ha b hb he
      by_contra hne
      rcases le_total (rank a) (rank b) with hab | hba
      · exact hs ha hb hne ⟨he, hab⟩
      · exact hs hb ha (Ne.symm hne) ⟨he.symm, hba⟩
    calc
      s.card = (s.image colour).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ Fintype.card (Fin w) := Finset.card_le_univ _
      _ = w := Fintype.card_fin w
  apply algebra_generating_finset_le_of_operator_leading_width hd C hC a0
    rel (fun _ => ⟨rfl, le_rfl⟩) _ w hwidth
  intro v a b hv hab
  obtain ⟨hcolour, hle⟩ := hab
  have hwalk : ∀ t (a : Fin n) (v : M), rank b - rank a = t →
      colour a = colour b → rank a ≤ rank b →
      FiniteRowLeadingWeight.HasLeading (C v) a →
      ∃ r : A, FiniteRowLeadingWeight.HasLeading (C (r • v)) b := by
    intro t
    induction t with
    | zero =>
      intro a v hdiff hc hr hv
      have he : a = b := hlabels a b hc (by omega)
      subst a
      exact ⟨1, by simpa only [one_smul] using hv⟩
    | succ t ih =>
      intro a v hdiff hc hr hv
      have hlt : rank a < rank b := by omega
      obtain ⟨hnc, hnr⟩ := hadvance a b hc hlt
      obtain ⟨r, hrv⟩ := hnext v a hv
      obtain ⟨s, hsv⟩ := ih (next a) (r • v) (by omega) (hnc.trans hc) (by omega) hrv
      exact ⟨s * r, by simpa only [mul_smul] using hsv⟩
  exact hwalk _ a v rfl hcolour hle hv

end SymmetricSubgroupAsymptotics
