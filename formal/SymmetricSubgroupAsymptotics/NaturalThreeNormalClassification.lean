import SymmetricSubgroupAsymptotics.NaturalFourNormalChains

/-! The normal-subgroup trichotomy of the literal symmetric group on
three points. Only six-element commutator and conjugacy identities are
finite reductions. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NaturalThreeNormalClassification
abbrev G := Equiv.Perm (Fin 3)

private theorem cubic_commutator : ∀ g : G, g≠1 → ∃ h : G,
    (g*h*g⁻¹*h⁻¹)^3=1 ∧ g*h*g⁻¹*h⁻¹≠1 := by decide +kernel

private theorem cubic_conjugates : ∀ x : G, x^3=1 → x≠1 →
    ∀ y : G, y∈alternatingGroup (Fin 3) → y=1 ∨ ∃ h : G, h*x*h⁻¹=y := by
  change ∀ x : G, x^3=1 → x≠1 → ∀ y : G,
    Equiv.Perm.sign y=1 → y=1 ∨ ∃ h : G, h*x*h⁻¹=y
  decide +kernel

theorem alternating_le_nontrivial_normal (N : Subgroup G) (hN : N.Normal)
    (hn : N≠⊥) : alternatingGroup (Fin 3)≤N := by
  obtain ⟨g,hgn⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hn
  obtain ⟨h,hcube,hne⟩ := cubic_commutator (g : G) (fun he => hgn (Subtype.ext he))
  have hx : (g : G)*h*(g : G)⁻¹*h⁻¹∈N := by
    have hh := hN.conj_mem ((g : G)⁻¹) (N.inv_mem g.property) h
    simpa only [mul_assoc] using N.mul_mem g.property hh
  intro y hy
  rcases cubic_conjugates _ hcube hne y hy with he | ⟨k,hk⟩
  · rw [he]; exact N.one_mem
  · rw [← hk]; exact hN.conj_mem _ hx k

theorem normal_trichotomy (N : Subgroup G) (hN : N.Normal) :
    N=⊥ ∨ N=alternatingGroup (Fin 3) ∨ N=⊤ := by
  by_cases hn : N=⊥
  · exact Or.inl hn
  have hAN := alternating_le_nontrivial_normal N hN hn
  have hm := Subgroup.relIndex_mul_index hAN
  rw [alternatingGroup.index_eq_two] at hm
  have hd : N.index∣2 := ⟨(alternatingGroup (Fin 3)).relIndex N,
    by simpa only [Nat.mul_comm] using hm.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hi | hi
  · exact Or.inr (Or.inr (Subgroup.index_eq_one.mp hi))
  · have hr : (alternatingGroup (Fin 3)).relIndex N=1 := by rw [hi] at hm; omega
    exact Or.inr (Or.inl (le_antisymm (Subgroup.relIndex_eq_one.mp hr) hAN))

end SymmetricSubgroupAsymptotics.NaturalThreeNormalClassification
