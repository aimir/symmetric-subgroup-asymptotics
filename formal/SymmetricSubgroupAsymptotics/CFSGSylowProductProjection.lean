import Mathlib.GroupTheory.Sylow

/-! An actual Sylow subgroup of a finite direct product contains the
pure coordinate projections of each of its elements. Its underlying
subgroup is exactly the product of its two actual projection images. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSylowProductProjection

variable {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
  {p : ℕ} [Fact p.Prime]

theorem prod_isPGroup (H : Subgroup A) (K : Subgroup B)
    (hH : IsPGroup p H) (hK : IsPGroup p K) : IsPGroup p (H.prod K) := by
  obtain ⟨a, ha⟩ := hH.exists_card_eq
  obtain ⟨b, hb⟩ := hK.exists_card_eq
  apply IsPGroup.of_card (n := a + b)
  rw [Nat.card_congr (H.prodEquiv K).toEquiv, Nat.card_prod, ha, hb, pow_add]

theorem coe_eq_prod_maps (P : Sylow p (A × B)) :
    (P : Subgroup (A × B)) =
      ((P : Subgroup (A × B)).map (MonoidHom.fst A B)).prod
        ((P : Subgroup (A × B)).map (MonoidHom.snd A B)) := by
  let H := (P : Subgroup (A × B)).map (MonoidHom.fst A B)
  let K := (P : Subgroup (A × B)).map (MonoidHom.snd A B)
  have hHK : IsPGroup p (H.prod K) := prod_isPGroup H K
    (P.isPGroup'.map (MonoidHom.fst A B)) (P.isPGroup'.map (MonoidHom.snd A B))
  have hle : (P : Subgroup (A × B)) ≤ H.prod K := by
    intro g hg
    exact ⟨⟨g, hg, rfl⟩, ⟨g, hg, rfl⟩⟩
  exact (P.3 hHK hle).symm

theorem fst_pure_mem (P : Sylow p (A × B)) {g : A × B} (hg : g ∈ P) :
    (g.1, 1) ∈ P := by
  change (g.1, 1) ∈ (P : Subgroup (A × B))
  rw [show (P : Subgroup (A × B)) = _ from coe_eq_prod_maps P]
  exact ⟨⟨g, hg, rfl⟩, ((P : Subgroup (A × B)).map (MonoidHom.snd A B)).one_mem⟩

theorem snd_pure_mem (P : Sylow p (A × B)) {g : A × B} (hg : g ∈ P) :
    (1, g.2) ∈ P := by
  change (1, g.2) ∈ (P : Subgroup (A × B))
  rw [show (P : Subgroup (A × B)) = _ from coe_eq_prod_maps P]
  exact ⟨((P : Subgroup (A × B)).map (MonoidHom.fst A B)).one_mem, ⟨g, hg, rfl⟩⟩

end SymmetricSubgroupAsymptotics.CFSGSylowProductProjection
