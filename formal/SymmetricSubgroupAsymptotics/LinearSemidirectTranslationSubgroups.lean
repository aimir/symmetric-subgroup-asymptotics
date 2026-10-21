import SymmetricSubgroupAsymptotics.LinearSemidirectCoprimeSocleBounds

/-! Actual translation subspaces in a displayed linear semidirect product.
Invariance proves normality; no finite group table or chosen extension
class is substituted for the literal subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.LinearSemidirectCoprimeSocleBounds
open SemidirectProduct
variable {p : ℕ} [Fact p.Prime] {R V : Type}
    [Group R] [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V]
    (rho : R →* (V ≃ₗ[ZMod p] V))

def translationSpace (B : Submodule (ZMod p) V) : Subgroup (Model rho) where
  carrier := {g | g.right = 1 ∧ g.left.toAdd ∈ B}
  one_mem' := ⟨rfl, B.zero_mem⟩
  mul_mem' := by
    intro x y hx hy
    constructor
    · change x.right * y.right = 1
      rw [hx.1, hy.1, one_mul]
    · change x.left.toAdd + rho x.right y.left.toAdd ∈ B
      rw [hx.1, map_one]
      exact B.add_mem hx.2 hy.2
  inv_mem' := by
    intro x hx
    constructor
    · change x.right⁻¹ = 1
      rw [hx.1, inv_one]
    · change rho x.right⁻¹ (-x.left.toAdd) ∈ B
      rw [hx.1, inv_one, map_one]
      exact B.neg_mem hx.2

theorem translationSpace_normal (B : Submodule (ZMod p) V)
    (hB : ∀ r v, v ∈ B → rho r v ∈ B) : (translationSpace rho B).Normal := by
  constructor
  intro a ha g
  have hae : a = (inl a.left : Model rho) := by
    apply SemidirectProduct.ext
    · rfl
    · exact ha.1
  rw [hae, conjugate_translation]
  exact ⟨rfl, hB g.right a.left.toAdd ha.2⟩

def translationSpaceEquiv (B : Submodule (ZMod p) V) :
    translationSpace rho B ≃ Multiplicative B where
  toFun g := Multiplicative.ofAdd ⟨g.val.left.toAdd, g.property.2⟩
  invFun v := ⟨inl (Multiplicative.ofAdd v.toAdd.val), rfl, v.toAdd.property⟩
  left_inv g := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · exact g.property.1.symm
  right_inv _ := rfl

theorem translationSpace_card (B : Submodule (ZMod p) V) :
    Nat.card (translationSpace rho B) = Nat.card B :=
  Nat.card_congr (translationSpaceEquiv rho B)

@[simp] theorem inl_mem_translationSpace (B : Submodule (ZMod p) V) (v : V) :
    (inl (Multiplicative.ofAdd v) : Model rho) ∈ translationSpace rho B ↔ v ∈ B :=
  and_iff_right rfl

end SymmetricSubgroupAsymptotics.LinearSemidirectCoprimeSocleBounds
