import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixNormalGenerators

/-! The published primitive-six alternatives have no abelian normal
subgroup, and every nonzero normal image leaves quotient order at most
two. Both properties concern the exact original top, via actual equivalences. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveDegreeSixTopNormalDichotomy

/-- Neither choice of finite enumeration nor decidable equality changes
this literal subgroup. Both choices must be transported together. -/
private theorem alternatingGroup_instances (X : Type)
    (f₁ f₂ : Fintype X) (d₁ d₂ : DecidableEq X) :
    @alternatingGroup X f₁ d₁ = @alternatingGroup X f₂ d₂ := by
  have hf : f₁=f₂ := Subsingleton.elim _ _
  have hd : d₁=d₂ := Subsingleton.elim _ _
  cases hf
  cases hd
  rfl

private theorem image_commutative {G H : Type} [Group G] [Group H]
    (f : G →* H) (N : Subgroup G) (hc : IsMulCommutative N) :
    IsMulCommutative (N.map f) := by
  apply IsMulCommutative.of_comm
  rintro ⟨x,hx⟩ ⟨y,hy⟩
  rcases hx with ⟨g,hg,rfl⟩
  rcases hy with ⟨h,hh,rfl⟩
  apply Subtype.ext
  change f g * f h=f h * f g
  rw [← map_mul,← map_mul]
  exact congrArg f (congrArg Subtype.val (hc.is_comm.comm (⟨g,hg⟩ : N) ⟨h,hh⟩))

private theorem noAbelian_of_equiv {G H : Type} [Group G] [Group H]
    (e : G ≃* H)
    (hH : ∀ N : Subgroup H, N.Normal → IsMulCommutative N → N=⊥)
    (N : Subgroup G) (hN : N.Normal) (hc : IsMulCommutative N) : N=⊥ := by
  have hm := hH (N.map e.toMonoidHom) (hN.map _ e.surjective)
    (image_commutative e.toMonoidHom N hc)
  apply le_antisymm _ bot_le
  have hle := (Subgroup.map_eq_bot_iff (H := N)).mp hm
  have hk : e.toMonoidHom.ker=⊥ := (MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective
  exact hle.trans hk.le

private theorem smallQuotient_of_equiv {G H : Type} [Group G] [Group H]
    (e : G ≃* H)
    (hH : ∀ N : Subgroup H, N.Normal → N≠⊥ → Nat.card (H ⧸ N) ≤ 2)
    (N : Subgroup G) (hN : N.Normal) (hne : N≠⊥) : Nat.card (G ⧸ N) ≤ 2 := by
  letI := hN
  let M := N.map e.toMonoidHom
  letI : M.Normal := hN.map _ e.surjective
  have hm : M≠⊥ := by
    intro hz
    apply hne
    apply le_antisymm _ bot_le
    have hle := (Subgroup.map_eq_bot_iff (H := N)).mp hz
    have hk : e.toMonoidHom.ker=⊥ := (MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective
    exact hle.trans hk.le
  have he := Nat.card_congr (QuotientGroup.congr N M e rfl).toEquiv
  exact he.le.trans (hH M inferInstance hm)

private theorem alternating_noncommutative (n : ℕ) (hn : 5 ≤ n) :
    ¬ IsMulCommutative (alternatingGroup (Fin n)) := by
  rw [alternatingGroup.isMulCommutative_iff_card_le_three]
  simpa using (show ¬ n ≤ 3 by omega)

private theorem alternating_noAbelian (n : ℕ) (hn : 5 ≤ n)
    (N : Subgroup (alternatingGroup (Fin n))) (hN : N.Normal)
    (hc : IsMulCommutative N) : N=⊥ := by
  letI := alternatingGroup.isSimpleGroup (α := Fin n) (by simpa using hn)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N hN with h | h
  · exact h
  · have hfull : IsMulCommutative (alternatingGroup (Fin n)) :=
      IsMulCommutative.of_comm fun x y => by
        have hx : x∈N := by rw [h]; exact Subgroup.mem_top x
        have hy : y∈N := by rw [h]; exact Subgroup.mem_top y
        exact congrArg Subtype.val (hc.is_comm.comm (⟨x,hx⟩ : N) ⟨y,hy⟩)
    exact (alternating_noncommutative n hn hfull).elim

private theorem alternating_smallQuotient (n : ℕ) (hn : 5 ≤ n)
    (N : Subgroup (alternatingGroup (Fin n))) (hN : N.Normal) (hne : N≠⊥) :
    Nat.card (alternatingGroup (Fin n) ⧸ N) ≤ 2 := by
  letI := hN
  letI := alternatingGroup.isSimpleGroup (α := Fin n) (by simpa using hn)
  have htop := (IsSimpleGroup.eq_bot_or_eq_top_of_normal N hN).resolve_left hne
  rw [htop, ← Subgroup.index_eq_card, Subgroup.index_top]
  decide

private theorem symmetric_noAbelian (n : ℕ) (hn : 5 ≤ n)
    (N : Subgroup (Equiv.Perm (Fin n))) (hN : N.Normal)
    (hc : IsMulCommutative N) : N=⊥ := by
  by_contra hne
  have ha : alternatingGroup (Fin n) ≤ N := by
    rcases AlternatingSymmetricNormalChain.symmetric_normal_classification
      (by simpa using hn) N hN with h | h | h
    · exact (hne h).elim
    · have hcanonical : N =
          @alternatingGroup (Fin n) (Fin.fintype n) (instDecidableEqFin n) :=
        h.trans (alternatingGroup_instances (Fin n) _ _ _ _)
      exact hcanonical.symm.le
    · rw [h]; exact le_top
  apply alternating_noncommutative n hn
  apply IsMulCommutative.of_comm
  intro x y
  apply Subtype.ext
  change x.1 * y.1 = y.1 * x.1
  exact congrArg (fun z : N => (z : Equiv.Perm (Fin n))) (hc.is_comm.comm
    (⟨x.1,ha x.2⟩ : N) ⟨y.1,ha y.2⟩)

private theorem symmetric_smallQuotient (n : ℕ) (hn : 5 ≤ n)
    (N : Subgroup (Equiv.Perm (Fin n))) (hN : N.Normal) (hne : N≠⊥) :
    Nat.card (Equiv.Perm (Fin n) ⧸ N) ≤ 2 := by
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  letI := hN
  rcases AlternatingSymmetricNormalChain.symmetric_normal_classification
    (by simpa using hn) N hN with h | h | h
  · exact (hne h).elim
  · have hcanonical : N =
        @alternatingGroup (Fin n) (Fin.fintype n) (instDecidableEqFin n) :=
      h.trans (alternatingGroup_instances (Fin n) _ _ _ _)
    rw [hcanonical, ← Subgroup.index_eq_card]
    exact (@alternatingGroup.index_eq_two (Fin n) (Fin.fintype n)
      (instDecidableEqFin n) inferInstance).le
  · rw [h, ← Subgroup.index_eq_card, Subgroup.index_top]
    decide

/-- Exact normal-top alternatives used for every original normal axis. -/
theorem properties (h6 : PublishedPrimitiveDegreeSixClassification)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X]
    (hdegree : Nat.card X=6) :
    (∀ N : Subgroup G, N.Normal → IsMulCommutative N → N=⊥) ∧
    (∀ N : Subgroup G, N.Normal → N≠⊥ → Nat.card (G ⧸ N) ≤ 2) := by
  rcases h6 G X hdegree with h | h | h | h <;> rcases h with ⟨e⟩
  · exact ⟨noAbelian_of_equiv e (alternating_noAbelian 5 (by decide)),
      smallQuotient_of_equiv e (alternating_smallQuotient 5 (by decide))⟩
  · exact ⟨noAbelian_of_equiv e (symmetric_noAbelian 5 (by decide)),
      smallQuotient_of_equiv e (symmetric_smallQuotient 5 (by decide))⟩
  · exact ⟨noAbelian_of_equiv e (alternating_noAbelian 6 (by decide)),
      smallQuotient_of_equiv e (alternating_smallQuotient 6 (by decide))⟩
  · exact ⟨noAbelian_of_equiv e (symmetric_noAbelian 6 (by decide)),
      smallQuotient_of_equiv e (symmetric_smallQuotient 6 (by decide))⟩

end SymmetricSubgroupAsymptotics.PrimitiveDegreeSixTopNormalDichotomy
