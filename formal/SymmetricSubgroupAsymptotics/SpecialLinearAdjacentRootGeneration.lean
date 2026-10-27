import SymmetricSubgroupAsymptotics.CFSGTypeAElementaryGeneration

/-! Adjacent positive and negative root groups generate the literal SL.
The proof uses actual matrix commutators along the original coordinate line. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.SpecialLinearAdjacentRootGeneration
open CFSGTypeAElementaryMatrices
variable {F : Type*} [Field F] {n : ℕ}

theorem eq_top (H : Subgroup (SL (n := Fin (n+1)) (F := F)))
    (hEdge : ∀ (i j : Fin (n+1)) (hij : i ≠ j),
      (i.val+1=j.val ∨ j.val+1=i.val) → ∀ a : F, elementary hij a ∈ H) : H=⊤ := by
  have hc : ∀ x y : SL (n := Fin (n+1)) (F := F),
      x ∈ H → y ∈ H → ⁅x,y⁆ ∈ H := by
    intro x y hx hy
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)
  have hSpan : ∀ (d : ℕ) (i j : Fin (n+1)), 0<d → i.val+d=j.val →
      ∀ (hij : i ≠ j) (a : F), elementary hij a ∈ H ∧ elementary hij.symm a ∈ H := by
    intro d
    induction d with
    | zero => intro i j hd; omega
    | succ d ih =>
      intro i j hd he hij a
      by_cases hz : d=0
      · subst d
        exact ⟨hEdge i j hij (Or.inl (by omega)) a,
          hEdge j i hij.symm (Or.inr (by omega)) a⟩
      have hdpos : 0<d := Nat.pos_of_ne_zero hz
      let k : Fin (n+1) := ⟨i.val+d, by omega⟩
      have hik : i ≠ k := by intro h; have := congrArg Fin.val h; dsimp [k] at this; omega
      have hkj : k ≠ j := by intro h; have := congrArg Fin.val h; dsimp [k] at this; omega
      have hkedge : k.val+1=j.val := by dsimp [k]; omega
      have hkspan : i.val+d=k.val := rfl
      have hleft := ih i k hdpos hkspan hik a
      have hright := ih i k hdpos hkspan hik (1 : F)
      constructor
      · have h := hc (elementary hik a) (elementary hkj (1 : F)) hleft.1
          (hEdge k j hkj (Or.inl hkedge) 1)
        rw [elementary_commutator hik hkj hij,mul_one] at h
        exact h
      · have h := hc (elementary hkj.symm a) (elementary hik.symm (1 : F))
          (hEdge j k hkj.symm (Or.inr hkedge) a) hright.2
        rw [elementary_commutator hkj.symm hik.symm hij.symm,mul_one] at h
        exact h
  apply CFSGTypeAElementaryGeneration.eq_top_of_elementary H
  intro i j hij a
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (hSpan (j.val-i.val) i j (by omega) (by omega) hij a).1
  · exact (hSpan (i.val-j.val) j i (by omega) (by omega) hij.symm a).2

/-- The adjacent roots in both orientations suffice. No dimension or field-size
restriction is needed for elementary generation itself. -/
theorem eq_top_of_simple_roots (H : Subgroup (SL (n := Fin (n+1)) (F := F)))
    (hPositive : ∀ i : Fin n, ∀ a : F,
      elementary (show i.castSucc ≠ i.succ by intro h; have := congrArg Fin.val h; simp only [Fin.val_castSucc, Fin.val_succ] at this; omega) a ∈ H)
    (hNegative : ∀ i : Fin n, ∀ a : F,
      elementary (show i.succ ≠ i.castSucc by intro h; have := congrArg Fin.val h; simp only [Fin.val_castSucc, Fin.val_succ] at this; omega) a ∈ H) : H=⊤ := by
  apply eq_top H
  intro i j hij h a
  rcases h with h | h
  · let k : Fin n := ⟨i.val, by omega⟩
    have hi : i=k.castSucc := Fin.ext rfl
    have hj : j=k.succ := Fin.ext (by simpa [k] using h.symm)
    simpa only [hi,hj] using hPositive k a
  · let k : Fin n := ⟨j.val, by omega⟩
    have hi : i=k.succ := Fin.ext (by simpa [k] using h.symm)
    have hj : j=k.castSucc := Fin.ext rfl
    simpa only [hi,hj] using hNegative k a

end SymmetricSubgroupAsymptotics.SpecialLinearAdjacentRootGeneration
