import SymmetricSubgroupAsymptotics.CFSGSylowNormalizerGeneration

/-! Two proper overgroups suffice to choose a generating normalizer
conjugate. The transporter assertion is Sylow conjugacy in the actual
overgroup, not an assumed ambient conjugacy or generation recognition. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.SylowNormalizerTwoOvergroups

variable {G : Type*} [Group G]

theorem exists_outside_two (A B : Subgroup G) (hA : A ≠ ⊤) (hB : B ≠ ⊤) :
    ∃ g : G, g ∉ A ∧ g ∉ B := by
  obtain ⟨a, ha⟩ : ∃ a : G, a ∉ A := by
    by_contra! h
    exact hA (top_unique (fun g _ => h g))
  obtain ⟨b, hb⟩ : ∃ b : G, b ∉ B := by
    by_contra! h
    exact hB (top_unique (fun g _ => h g))
  by_cases haB : a ∈ B
  · by_cases hbA : b ∈ A
    · refine ⟨a * b, ?_, ?_⟩
      · intro hh
        exact ha (by simpa only [mul_inv_cancel_right] using A.mul_mem hh (A.inv_mem hbA))
      · intro hh
        exact hb (by simpa only [inv_mul_cancel_left] using B.mul_mem (B.inv_mem haB) hh)
    · exact ⟨b, hbA, hb⟩
  · exact ⟨a, ha, haB⟩

theorem conjugator_mem [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (K : Subgroup G) (hNK : Subgroup.normalizer (P : Set G) ≤ K)
    (g : G) (hPg : ((g • P : Sylow p G) : Subgroup G) ≤ K) : g ∈ K := by
  have hPK : (P : Subgroup G) ≤ K := Subgroup.le_normalizer.trans hNK
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K ((g • P).subtype hPg) (P.subtype hPK)
  simp_rw [Sylow.smul_subtype, Subgroup.smul_def, smul_smul] at hk
  have hkg : (k : G) * g ∈ Subgroup.normalizer (P : Set G) :=
    Sylow.smul_eq_iff_mem_normalizer.mp (Sylow.subtype_injective hk)
  have hh := K.mul_mem (K.inv_mem k.property) (hNK hkg)
  simpa only [inv_mul_cancel_left] using hh

theorem conjugates_generate [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (A B : Subgroup G) (hNA : Subgroup.normalizer (P : Set G) ≤ A)
    (hNB : Subgroup.normalizer (P : Set G) ≤ B) (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (hover : ∀ K : Subgroup G, Subgroup.normalizer (P : Set G) ≤ K →
      K = Subgroup.normalizer (P : Set G) ∨ K = A ∨ K = B ∨ K = ⊤) :
    ∃ g : G, Subgroup.closure (((Subgroup.normalizer (P : Set G)) : Set G) ∪
      (Subgroup.normalizer (P : Set G)).map (MulAut.conj g).toMonoidHom) = ⊤ := by
  obtain ⟨g, hgA, hgB⟩ := exists_outside_two A B hA hB
  let N := Subgroup.normalizer (P : Set G)
  let K := N ⊔ N.map (MulAut.conj g).toMonoidHom
  have hNK : N ≤ K := le_sup_left
  have hmap : (P : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ K :=
    (Subgroup.map_mono Subgroup.le_normalizer).trans le_sup_right
  have hPg : ((g • P : Sylow p G) : Subgroup G) ≤ K := by
    simpa only [Sylow.smul_def, Sylow.pointwise_smul_def,
      Subgroup.pointwise_smul_def] using hmap
  have hgK : g ∈ K := conjugator_mem P K hNK g hPg
  have htop : K = ⊤ := by
    rcases hover K hNK with he | he | he | he
    · exact (hgA (hNA (he ▸ hgK))).elim
    · exact (hgA (he ▸ hgK)).elim
    · exact (hgB (he ▸ hgK)).elim
    · exact he
  refine ⟨g, ?_⟩
  simpa only [Subgroup.closure_union, Subgroup.closure_eq] using htop

end SymmetricSubgroupAsymptotics.SylowNormalizerTwoOvergroups
