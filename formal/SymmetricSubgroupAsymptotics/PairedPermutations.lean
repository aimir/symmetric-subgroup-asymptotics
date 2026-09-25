import SymmetricSubgroupAsymptotics.BinaryHeisenberg

/-! The literal centralizer of a simultaneous flip on paired points. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- A permutation of the pairs, with an independently chosen flip on each
source pair. -/
def pairedPermutation {α : Type*} (σ : Equiv.Perm α) (f : α → ZMod 2) :
    Equiv.Perm (α × ZMod 2) where
  toFun x := (σ x.1, x.2 + f x.1)
  invFun x := (σ.symm x.1, x.2 + f (σ.symm x.1))
  left_inv x := by ext <;> simp [add_comm, add_left_comm]
  right_inv x := by ext <;> simp [add_comm, add_left_comm]

/-- The central flip interchanges the two points in every pair. -/
def pairedFlip (α : Type*) : Equiv.Perm (α × ZMod 2) :=
  pairedPermutation (Equiv.refl α) (fun _ => 1)

/-- All literal permutations commuting with the paired flip. -/
def pairedCentralizer (α : Type*) : Subgroup (Equiv.Perm (α × ZMod 2)) :=
  Subgroup.centralizer {pairedFlip α}

theorem pairedPermutation_mem_centralizer {α : Type*}
    (σ : Equiv.Perm α) (f : α → ZMod 2) :
    pairedPermutation σ f ∈ pairedCentralizer α := by
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  ext x <;> simp [pairedPermutation, pairedFlip, add_assoc, add_comm, add_left_comm]

/-- Commutation with the flip determines both points of every pair from the
image of its zero point. -/
theorem pairedCentralizer_apply {α : Type*} (h : pairedCentralizer α) (x : α) (z : ZMod 2) :
    (h : Equiv.Perm (α × ZMod 2)) (x, z) =
      (((h : Equiv.Perm (α × ZMod 2)) (x, 0)).1,
        z + ((h : Equiv.Perm (α × ZMod 2)) (x, 0)).2) := by
  have hc := Subgroup.mem_centralizer_singleton_iff.mp h.2
  have hz : z = 0 ∨ z = 1 := by
    have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    exact h z
  rcases hz with rfl | rfl
  · simp
  · have he := Equiv.congr_fun hc (x, 0)
    simpa [pairedFlip, pairedPermutation, add_comm] using he

/-- The induced actual permutation of pairs. -/
def pairedBasePermutation {α : Type*} (h : pairedCentralizer α) : Equiv.Perm α where
  toFun x := ((h : Equiv.Perm (α × ZMod 2)) (x, 0)).1
  invFun x := ((h⁻¹ : Equiv.Perm (α × ZMod 2)) (x, 0)).1
  left_inv x := by
    have he := congrArg Prod.fst
      (pairedCentralizer_apply h⁻¹ ((h : Equiv.Perm (α × ZMod 2)) (x, 0)).1
        ((h : Equiv.Perm (α × ZMod 2)) (x, 0)).2)
    simpa using he.symm
  right_inv x := by
    have he := congrArg Prod.fst
      (pairedCentralizer_apply h ((h⁻¹ : Equiv.Perm (α × ZMod 2)) (x, 0)).1
        ((h⁻¹ : Equiv.Perm (α × ZMod 2)) (x, 0)).2)
    simpa using he.symm

/-- Explicit pair-permutation and flip coordinates on the entire centralizer. -/
def pairedCentralizerEquiv (α : Type*) :
    pairedCentralizer α ≃ Equiv.Perm α × (α → ZMod 2) where
  toFun h := (pairedBasePermutation h, fun x => ((h : Equiv.Perm (α × ZMod 2)) (x, 0)).2)
  invFun p := ⟨pairedPermutation p.1 p.2, pairedPermutation_mem_centralizer p.1 p.2⟩
  left_inv h := by
    apply Subtype.ext
    apply Equiv.ext
    rintro ⟨x, z⟩
    exact (pairedCentralizer_apply h x z).symm
  right_inv p := by
    apply Prod.ext
    · apply Equiv.ext
      intro x
      simp [pairedBasePermutation, pairedPermutation]
    · funext x
      simp [pairedPermutation]

/-- The full centralizer has the original pair-wreath order. -/
theorem pairedCentralizer_card (α : Type*) [Fintype α] :
    Nat.card (pairedCentralizer α) = (Fintype.card α).factorial * 2 ^ Fintype.card α := by
  classical
  rw [Nat.card_congr (pairedCentralizerEquiv α)]
  simp [Nat.card_eq_fintype_card, Fintype.card_perm]

end SymmetricSubgroupAsymptotics
