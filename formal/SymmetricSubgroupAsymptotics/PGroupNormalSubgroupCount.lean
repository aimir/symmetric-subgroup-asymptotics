import SymmetricSubgroupAsymptotics.PGroupNormalIndexP

/-! Bounded-index counts of actual ambient-normal subgroups. A uniform
bound for the original ambient relative heads gives the sharp cumulative
bound p^(a*d). The counted subgroups, their indices, and all conjugations
remain in the original group. This is not a bound by absolute subgroup
rank and does not use monotonicity of generator numbers. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- The literal G-normal subgroups inside M with bounded actual relative
index. The original normality evidence is retained in the subtype. -/
abbrev NormalSubgroupsAtMostIndex (M : Subgroup G) (k : ℕ) :=
  {H : Subgroup G // H.Normal ∧ H ≤ M ∧ H.relIndex M ≤ k}

/-- Increasing the p-power index cutoff adds at most one index-p child
per nonzero invariant character of each subgroup at the previous cutoff. -/
theorem pGroup_normal_subgroup_count_step (hG : IsPGroup p G)
    (M : Subgroup G) [M.Normal] (a d : ℕ)
    (hd : ∀ (L : Subgroup G) [L.Normal], L ≤ M →
      Module.finrank (ZMod p) (primeRelativeCharacters p L) ≤ d) :
    Nat.card (NormalSubgroupsAtMostIndex M (p ^ (a+1))) ≤
      Nat.card (NormalSubgroupsAtMostIndex M (p ^ a)) * p ^ d := by
  classical
  let A := NormalSubgroupsAtMostIndex M (p ^ a)
  let B := NormalSubgroupsAtMostIndex M (p ^ (a+1))
  let C (J : A) :=
    {H : Subgroup G // H.Normal ∧ H ≤ J.1 ∧ H.relIndex J.1 = p}
  let T := A ⊕ Σ J : A, C J
  let underlying : T → Subgroup G := fun t =>
    match t with
    | Sum.inl J => J.1
    | Sum.inr z => z.2.1
  have hex (H : B) : ∃ t : T, underlying t = H.1 := by
    by_cases hsmall : H.1.relIndex M ≤ p ^ a
    · exact ⟨Sum.inl ⟨H.1,H.2.1,H.2.2.1,hsmall⟩,rfl⟩
    · letI : H.1.Normal := H.2.1
      have hHM : H.1 < M := lt_of_le_of_ne H.2.2.1 (by
        intro he
        apply hsmall
        rw [he,Subgroup.relIndex_self]
        exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))
      obtain ⟨J,hJ,hHJ,hJM,hindex⟩ :=
        pGroup_normal_interval_bottom_step hG H.1 M hHM
      have hJindex : J.relIndex M ≤ p ^ a := by
        apply Nat.le_of_mul_le_mul_left _ (Fact.out : p.Prime).pos
        calc
          p * J.relIndex M = H.1.relIndex M := by
            exact (congrArg (fun t => t*J.relIndex M) hindex.symm).trans
              (Subgroup.relIndex_mul_relIndex H.1 J M hHJ.le hJM)
          _ ≤ p ^ (a+1) := H.2.2.2
          _ = p * p ^ a := pow_succ' p a
      exact ⟨Sum.inr ⟨⟨J,hJ,hJM,hJindex⟩,⟨H.1,H.2.1,hHJ.le,hindex⟩⟩,rfl⟩
  let f : B → T := fun H => (hex H).choose
  have hf : Function.Injective f := by
    intro H K he
    apply Subtype.ext
    exact (hex H).choose_spec.symm.trans
      ((congrArg underlying he).trans (hex K).choose_spec)
  have hcard : Nat.card B ≤ Nat.card A + Nat.card (Σ J : A, C J) := by
    simpa only [T,Nat.card_sum] using Nat.card_le_card_of_injective f hf
  have hchild (J : A) : Nat.card (C J) ≤ p ^ d - 1 := by
    letI : J.1.Normal := J.2.1
    exact (pGroup_normal_index_p_count_le hG J.1).trans
      (Nat.sub_le_sub_right (Nat.pow_le_pow_right (Fact.out : p.Prime).pos
        (hd J.1 J.2.2.1)) 1)
  have hsum : Nat.card (Σ J : A, C J) ≤ Nat.card A * (p ^ d - 1) := by
    letI := Fintype.ofFinite A
    calc
      _ = ∑ J : A, Nat.card (C J) := Nat.card_sigma
      _ ≤ ∑ _J : A, (p ^ d - 1) := Finset.sum_le_sum (fun J _ => hchild J)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,
          Nat.card_eq_fintype_card]
  have hpos : 0 < p ^ d := pow_pos (Fact.out : p.Prime).pos _
  calc
    Nat.card B ≤ Nat.card A + Nat.card A * (p ^ d - 1) :=
      hcard.trans (Nat.add_le_add_left hsum _)
    _ = Nat.card A * (1 + (p ^ d - 1)) := by rw [Nat.mul_add,Nat.mul_one]
    _ = Nat.card A * p ^ d := by congr 1; omega

/-- Sharp cumulative normal-subgroup count, using a bound for the
whole-ambient relative character dimension of every original normal
subgroup below M. The bound includes M itself at index one. -/
theorem pGroup_normal_subgroup_count_le (hG : IsPGroup p G)
    (M : Subgroup G) [M.Normal] (d : ℕ)
    (hd : ∀ (L : Subgroup G) [L.Normal], L ≤ M →
      Module.finrank (ZMod p) (primeRelativeCharacters p L) ≤ d) (a : ℕ) :
    Nat.card (NormalSubgroupsAtMostIndex M (p ^ a)) ≤ p ^ (a*d) := by
  induction a with
  | zero =>
    have he (H : NormalSubgroupsAtMostIndex M (p ^ 0)) : H.1 = M := by
      have hne : H.1.relIndex M ≠ 0 := by
        change Nat.card (M ⧸ H.1.subgroupOf M) ≠ 0
        exact Nat.card_pos.ne'
      have hi : H.1.relIndex M = 1 := by
        have h := H.2.2.2
        simp only [pow_zero] at h
        omega
      exact le_antisymm H.2.2.1 (Subgroup.relIndex_eq_one.mp hi)
    letI : Subsingleton (NormalSubgroupsAtMostIndex M (p ^ 0)) :=
      ⟨fun H K => Subtype.ext ((he H).trans (he K).symm)⟩
    have hunit : Nat.card Unit = 1 := by simp [Nat.card_eq_fintype_card]
    simpa only [Nat.zero_mul,pow_zero,hunit] using
      (Nat.card_le_card_of_injective
        (fun _ : NormalSubgroupsAtMostIndex M (p ^ 0) => ())
        (fun _ _ _ => Subsingleton.elim _ _))
  | succ a ih =>
    calc
      _ ≤ Nat.card (NormalSubgroupsAtMostIndex M (p ^ a)) * p ^ d :=
        pGroup_normal_subgroup_count_step hG M a d hd
      _ ≤ p ^ (a*d) * p ^ d := Nat.mul_le_mul_right _ ih
      _ = p ^ ((a+1)*d) := by rw [Nat.add_mul,Nat.one_mul,pow_add]

end SymmetricSubgroupAsymptotics
