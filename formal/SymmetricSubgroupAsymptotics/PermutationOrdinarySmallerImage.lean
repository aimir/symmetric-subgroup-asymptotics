import SymmetricSubgroupAsymptotics.PermutationOrdinarySmallerActions

/-! The sharp smaller-degree statement applies to the actual
permutation image at degree three whenever that image is proper. No
cyclic-group chart or subgroup census is used to remove the exception. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PermutationOrdinarySmallerImage

/-- Transport the same literal permutation image to Fin(card Y),
preserving its actual properness at the exceptional degree. -/
theorem genRank_of_smaller_image (n : ℕ)
    (hbelow : ∀ (k : ℕ), k < n → ∀ L : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → L ≠ ⊤) →
        ∃ S : Finset L, Subgroup.closure (S : Set L) = ⊤ ∧ 2 * S.card ≤ k)
    {Y : Type} [Finite Y] (J : Subgroup (Equiv.Perm Y))
    (hlt : Nat.card Y < n) (hproper : Nat.card Y = 3 → J ≠ ⊤) :
    2 * MarkedC4.genRank J ≤ Nat.card Y := by
  let eY : Equiv.Perm Y ≃* Equiv.Perm (Fin (Nat.card Y)) :=
    (Finite.equivFin Y).permCongrHom
  let f : J →* Equiv.Perm (Fin (Nat.card Y)) := eY.toMonoidHom.comp J.subtype
  have hf : Function.Injective f := eY.injective.comp Subtype.val_injective
  let eJ : J ≃* f.range := MonoidHom.ofInjective (f := f) hf
  have hnot : Nat.card Y = 3 → f.range ≠ ⊤ := by
    intro hthree heq
    apply hproper hthree
    apply top_unique
    intro y _
    have hy : eY y ∈ f.range := by rw [heq]; trivial
    obtain ⟨x,hx⟩ := hy
    have hxy : (x : Equiv.Perm Y) = y := eY.injective hx
    exact hxy ▸ x.property
  obtain ⟨S,hgen,hcard⟩ := hbelow (Nat.card Y) hlt f.range hnot
  rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv eJ]
  exact (Nat.mul_le_mul_left 2 (MarkedC4.genRank_le hgen)).trans hcard

end SymmetricSubgroupAsymptotics.PermutationOrdinarySmallerImage
