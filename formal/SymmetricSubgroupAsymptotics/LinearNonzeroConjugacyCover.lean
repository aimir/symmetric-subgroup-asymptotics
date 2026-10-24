import SymmetricSubgroupAsymptotics.FixedFreeConjugacyClassCover
import SymmetricSubgroupAsymptotics.BilinearContragredientDuality

/-! Bind the generic fixed-free class cover to the literal nonzero-vector
action of a linear representation. Stabilizers remain the same original
subgroups as in the natural action on the full vector space. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.LinearNonzeroConjugacyCover
variable {G K V : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]

abbrev nonzeroAction (ρ : G →* (V ≃ₗ[K] V)) : MulAction G {v : V // v ≠ 0} where
  smul g v := ⟨ρ g v.1, by
    intro h
    apply v.2
    exact (ρ g).injective (h.trans (map_zero (ρ g)).symm)⟩
  one_smul v := by
    apply Subtype.ext
    change ρ (1 : G) v.1 = v.1
    rw [map_one]
    rfl
  mul_smul g h v := by
    apply Subtype.ext
    change ρ (g*h) v.1 = ρ g (ρ h v.1)
    rw [map_mul]
    rfl

theorem fixedFree_iff (ρ : G →* (V ≃ₗ[K] V)) (g : G) :
    letI := nonzeroAction ρ
    FixedFreeConjugacyClassCover.FixedFree (X := {v : V // v ≠ 0}) g ↔
      ∀ v : V, ρ g v = v → v = 0 := by
  letI := nonzeroAction ρ
  constructor
  · intro h v hv
    by_contra hn
    exact h ⟨v, hn⟩ (Subtype.ext hv)
  · intro h v hv
    exact v.2 (h v.1 (congrArg Subtype.val hv))

theorem stabilizer_eq (ρ : G →* (V ≃ₗ[K] V)) (v : V) (hv : v ≠ 0) :
    letI := BilinearContragredientDuality.naturalAction ρ
    letI := nonzeroAction ρ
    MulAction.stabilizer G (⟨v, hv⟩ : {v : V // v ≠ 0}) = MulAction.stabilizer G v := by
  letI := BilinearContragredientDuality.naturalAction ρ
  letI := nonzeroAction ρ
  ext g
  change (⟨ρ g v, _⟩ : {v : V // v ≠ 0}) = ⟨v, hv⟩ ↔ ρ g v = v
  exact ⟨congrArg Subtype.val, fun h => Subtype.ext h⟩

theorem class_card_le [Finite G] (ρ : G →* (V ≃ₗ[K] V)) (v : V) (hv : v ≠ 0)
    (htrans : ∀ w : V, w ≠ 0 → ∃ g : G, ρ g v = w) :
    letI := BilinearContragredientDuality.naturalAction ρ
    letI := nonzeroAction ρ
    Nat.card (ConjClasses G) ≤ Nat.card (ConjClasses (MulAction.stabilizer G v)) +
      Nat.card (FixedFreeConjugacyClassCover.FreeClasses
        (G := G) (X := {v : V // v ≠ 0})) := by
  letI := BilinearContragredientDuality.naturalAction ρ
  letI := nonzeroAction ρ
  have ht (w : {v : V // v ≠ 0}) :
      ∃ g : G, g • (⟨v,hv⟩ : {v : V // v ≠ 0}) = w := by
    obtain ⟨g, hg⟩ := htrans w.1 w.2
    exact ⟨g, Subtype.ext hg⟩
  have h := FixedFreeConjugacyClassCover.class_card_le_stabilizer_add_free
    (⟨v,hv⟩ : {v : V // v ≠ 0}) ht
  rw [stabilizer_eq ρ v hv] at h
  exact h

end SymmetricSubgroupAsymptotics.LinearNonzeroConjugacyCover
