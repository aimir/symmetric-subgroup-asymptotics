import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Data.Finite.Sum
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

/-! In a transitive action, each conjugacy class either has a fixed-free
representative or is met by the literal point stabilizer. A fusion
criterion then embeds the fixed-free classes into ambient conjugacy
classes. No bound on either class family is assumed here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.FixedFreeConjugacyClassCover
variable {G X : Type*} [Group G] [MulAction G X]

def FixedFree (g : G) : Prop := ∀ x : X, g • x ≠ x

def FreeClasses :=
  {c : ConjClasses G // ∃ g : G, ConjClasses.mk g = c ∧ FixedFree (X := X) g}

instance finiteFreeClasses [Finite G] : Finite (FreeClasses (G := G) (X := X)) :=
  Finite.of_injective (fun c : FreeClasses (G := G) (X := X) => c.val)
    Subtype.val_injective

def coverMap (x₀ : X) :
    ConjClasses (MulAction.stabilizer G x₀) ⊕ FreeClasses (G := G) (X := X) →
      ConjClasses G :=
  Sum.elim (ConjClasses.map (MulAction.stabilizer G x₀).subtype) Subtype.val

theorem coverMap_surjective (x₀ : X)
    (htrans : ∀ x : X, ∃ a : G, a • x₀ = x) :
    Function.Surjective (coverMap (G := G) x₀) := by
  classical
  intro c
  obtain ⟨g, hg⟩ := ConjClasses.mk_surjective c
  by_cases hfree : FixedFree (X := X) g
  · exact ⟨Sum.inr ⟨c, g, hg, hfree⟩, rfl⟩
  · obtain ⟨y, hy⟩ := not_forall.mp hfree
    have hgy : g • y = y := not_not.mp hy
    obtain ⟨a, ha⟩ := htrans y
    have ht : a⁻¹ * g * a ∈ MulAction.stabilizer G x₀ := by
      change (a⁻¹ * g * a) • x₀ = x₀
      rw [mul_smul, mul_smul, ha, hgy, ←ha, inv_smul_smul]
    refine ⟨Sum.inl (ConjClasses.mk ⟨a⁻¹ * g * a, ht⟩), ?_⟩
    change ConjClasses.mk (a⁻¹ * g * a) = c
    apply Eq.trans _ hg
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    exact isConj_iff.mpr ⟨a, by group⟩

theorem class_card_le_stabilizer_add_free [Finite G] (x₀ : X)
    (htrans : ∀ x : X, ∃ a : G, a • x₀ = x) :
    Nat.card (ConjClasses G) ≤ Nat.card (ConjClasses (MulAction.stabilizer G x₀)) +
      Nat.card (FreeClasses (G := G) (X := X)) := by
  have h := Nat.card_le_card_of_surjective (coverMap (G := G) x₀)
    (coverMap_surjective x₀ htrans)
  simpa only [Nat.card_sum] using h

def freeClassMap {A : Type*} [Group A] (f : G →* A) :
    FreeClasses (G := G) (X := X) → ConjClasses A :=
  fun c => ConjClasses.map f c.1

theorem freeClassMap_injective {A : Type*} [Group A] (f : G →* A)
    (hfuse : ∀ g h : G, FixedFree (X := X) g → IsConj (f g) (f h) → IsConj g h) :
    Function.Injective (freeClassMap (X := X) f) := by
  intro c d h
  obtain ⟨g, hg, hfree⟩ := c.2
  obtain ⟨k, hk, _⟩ := d.2
  have hm : ConjClasses.mk (f g) = ConjClasses.mk (f k) := by
    change ConjClasses.map f c.1 = ConjClasses.map f d.1 at h
    simpa only [←hg, ←hk] using h
  apply Subtype.ext
  exact hg.symm.trans ((ConjClasses.mk_eq_mk_iff_isConj.mpr
    (hfuse g k hfree (ConjClasses.mk_eq_mk_iff_isConj.mp hm))).trans hk)

end SymmetricSubgroupAsymptotics.FixedFreeConjugacyClassCover
