import SymmetricSubgroupAsymptotics.CFSGSupportedAlternatingGeneration

/-! Extension by the identity on a literal sum carrier. This installs
the supported alternating group required by the checked large-support
generation theorem, including the actual relabeling of its support. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingSumSupport

variable (Y : Type) [Fintype Y] [DecidableEq Y] (r : ℕ)

def extensionHom : Equiv.Perm Y →* Equiv.Perm (Y ⊕ Fin r) where
  toFun g := Equiv.sumCongr g (Equiv.refl (Fin r))
  map_one' := by ext x; cases x <;> rfl
  map_mul' g h := by ext x; cases x <;> rfl

@[simp] theorem extension_apply_left (g : Equiv.Perm Y) (y : Y) :
    extensionHom Y r g (Sum.inl y) = Sum.inl (g y) := rfl

@[simp] theorem extension_apply_right (g : Equiv.Perm Y) (i : Fin r) :
    extensionHom Y r g (Sum.inr i) = Sum.inr i := rfl

theorem extension_even (g : Equiv.Perm Y) (hg : g ∈ alternatingGroup Y) :
    extensionHom Y r g ∈ alternatingGroup (Y ⊕ Fin r) := by
  apply Equiv.Perm.mem_alternatingGroup.mpr
  change Equiv.Perm.sign (Equiv.sumCongr g (Equiv.refl (Fin r))) = 1
  rw [Equiv.Perm.sign_sumCongr, Equiv.Perm.mem_alternatingGroup.mp hg]
  simp

def leftSupport : Finset (Y ⊕ Fin r) :=
  Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩

def leftEquiv : Y ≃ leftSupport Y r := Equiv.ofBijective
  (fun y => ⟨Sum.inl y, Finset.mem_map.mpr ⟨y, Finset.mem_univ _, rfl⟩⟩)
  ⟨fun x y h => Sum.inl_injective (congrArg Subtype.val h), by
    intro x
    obtain ⟨y, _, hy⟩ := Finset.mem_map.mp x.property
    exact ⟨y, Subtype.ext hy⟩⟩

@[simp] theorem leftEquiv_apply (y : Y) :
    (leftEquiv Y r y).val = Sum.inl y := rfl

theorem leftSupport_card : (leftSupport Y r).card = Fintype.card Y := by
  simp only [leftSupport, Finset.card_map, Finset.card_univ]

theorem ofSubtype_eq_extension (p : Equiv.Perm (leftSupport Y r)) :
    Equiv.Perm.ofSubtype p = extensionHom Y r ((leftEquiv Y r).symm.permCongr p) := by
  apply Equiv.ext
  intro x
  cases x with
  | inl y =>
      have hy : Sum.inl y ∈ leftSupport Y r := (leftEquiv Y r y).property
      rw [Equiv.Perm.ofSubtype_apply_of_mem p hy, extension_apply_left]
      change (p (leftEquiv Y r y)).val =
        Sum.inl ((leftEquiv Y r).symm (p (leftEquiv Y r y)))
      exact (congrArg Subtype.val ((leftEquiv Y r).apply_symm_apply
        (p (leftEquiv Y r y)))).symm
  | inr i =>
      have hi : Sum.inr i ∉ leftSupport Y r := by
        intro h
        obtain ⟨y, _, hy⟩ := Finset.mem_map.mp h
        cases hy
      rw [Equiv.Perm.ofSubtype_apply_of_not_mem p hi, extension_apply_right]

theorem alternating_le_of_transitive_extension
    (G : Subgroup (Equiv.Perm (Y ⊕ Fin r))) [MulAction.IsPretransitive G (Y ⊕ Fin r)]
    (hsize : 3 ≤ Fintype.card Y) (hhalf : r < Fintype.card Y)
    (hG : ∀ a : alternatingGroup Y, extensionHom Y r a.val ∈ G) :
    alternatingGroup (Y ⊕ Fin r) ≤ G := by
  apply CFSGSupportedAlternatingGeneration.alternatingGroup_le_of_supported_alternating
    G (leftSupport Y r)
  · simpa only [leftSupport_card] using hsize
  · rw [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin, leftSupport_card]
    omega
  · rintro _ ⟨a, rfl⟩
    let b : alternatingGroup Y := ⟨(leftEquiv Y r).symm.permCongr a.val,
      Equiv.Perm.mem_alternatingGroup.mpr (by
        rw [Equiv.Perm.sign_permCongr]
        exact Equiv.Perm.mem_alternatingGroup.mp a.property)⟩
    change Equiv.Perm.ofSubtype a.val ∈ G
    rw [ofSubtype_eq_extension]
    exact hG b

end SymmetricSubgroupAsymptotics.CFSGAlternatingSumSupport
