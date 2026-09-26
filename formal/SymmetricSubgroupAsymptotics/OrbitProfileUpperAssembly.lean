import SymmetricSubgroupAsymptotics.OrbitProfileAssembly

/-!
# Upper assembly with original action normalizers

Naturality alone retains the full internal-symmetry denominator in an upper
bound. Every labeling fibre contains a free copy of the original symmetry
group, even when several atlases present the same subgroup.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

/-- Original internal symmetries inject into every nonempty labeling fibre.
No orbit fullness, transitivity, or separation of action types is required. -/
def orbitProfileSymmetryFibreEmbedding {ι : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {P : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → Prop}
    (hnatural : OrbitProfileFamilyNatural Ω m U P)
    (p : Equiv.Perm (OrbitProfilePoints Ω m) × {K // P K}) :
    orbitProfileSymmetries Ω m U ↪
      {q // orbitProfileLabelMap P q = orbitProfileLabelMap P p} where
  toFun w := ⟨(p.1 * (w : Equiv.Perm (OrbitProfilePoints Ω m)),
    ⟨relabelSubgroup (w : Equiv.Perm (OrbitProfilePoints Ω m))⁻¹ p.2.val,
      hnatural _ ((orbitProfileSymmetries Ω m U).inv_mem w.property) _ p.2.property⟩), by
        change relabelSubgroup (p.1 * (w : Equiv.Perm (OrbitProfilePoints Ω m)))
          (relabelSubgroup (w : Equiv.Perm (OrbitProfilePoints Ω m))⁻¹ p.2.val) = _
        rw [relabelSubgroup_mul]
        simp [orbitProfileLabelMap]⟩
  inj' := by
    intro w v h
    apply Subtype.ext
    exact mul_left_cancel (congrArg (fun q ↦ q.val.1) h)

private theorem card_mul_le_card_of_fibre_lower {A B : Type*} [Finite A] [Finite B]
    (f : A → B) (c : ℕ) (hf : ∀ b, c ≤ Nat.card {a // f a = b}) :
    Nat.card B * c ≤ Nat.card A := by
  classical
  letI : Fintype B := Fintype.ofFinite B
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  calc
    Nat.card B * c = ∑ _ : B, c := by simp [Nat.card_eq_fintype_card]
    _ ≤ ∑ b : B, Nat.card {a // f a = b} := Finset.sum_le_sum (fun b _ ↦ hf b)

/-- An invariant model family has the original atlas weight as an upper
bound, even if its actual subgroup image has additional presentations. -/
theorem assembledOrbitProfile_card_le {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {P : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → Prop}
    (hnatural : OrbitProfileFamilyNatural Ω m U P) :
    Nat.card (AssembledOrbitProfile P) ≤
      Nat.card (LabelledOrbitAtlas Ω m U) * Nat.card {K // P K} := by
  classical
  let f : Equiv.Perm (OrbitProfilePoints Ω m) × {K // P K} → AssembledOrbitProfile P :=
    fun p ↦ ⟨orbitProfileLabelMap P p, ⟨p, rfl⟩⟩
  have hf (H : AssembledOrbitProfile P) :
      Nat.card (orbitProfileSymmetries Ω m U) ≤ Nat.card {p // f p = H} := by
    obtain ⟨p, hp⟩ := H.property
    let e : {q // f q = H} ≃ {q // orbitProfileLabelMap P q = orbitProfileLabelMap P p} :=
      Equiv.subtypeEquivRight fun q ↦ by
        change (⟨orbitProfileLabelMap P q, ⟨q, rfl⟩⟩ : AssembledOrbitProfile P) = H ↔ _
        rw [Subtype.ext_iff]
        exact Iff.intro (fun h ↦ h.trans hp.symm) (fun h ↦ h.trans hp)
    rw [Nat.card_congr e]
    exact Nat.card_le_card_of_injective _ (orbitProfileSymmetryFibreEmbedding hnatural p).injective
  have hc := card_mul_le_card_of_fibre_lower f _ hf
  rw [Nat.card_prod] at hc
  have hg : Nat.card (Equiv.Perm (OrbitProfilePoints Ω m)) =
      Nat.card (LabelledOrbitAtlas Ω m U) * Nat.card (orbitProfileSymmetries Ω m U) := by
    rw [← Nat.card_congr (labelledOrbitProfileEquivAtlas Ω m U)]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup (orbitProfileSymmetries Ω m U)
  have hw : 0 < Nat.card (orbitProfileSymmetries Ω m U) := Nat.card_pos
  apply Nat.le_of_mul_le_mul_right ?_ hw
  calc
    Nat.card (AssembledOrbitProfile P) * Nat.card (orbitProfileSymmetries Ω m U) ≤
        Nat.card (Equiv.Perm (OrbitProfilePoints Ω m)) * Nat.card {K // P K} := hc
    _ = (Nat.card (LabelledOrbitAtlas Ω m U) * Nat.card {K // P K}) *
        Nat.card (orbitProfileSymmetries Ω m U) := by rw [hg]; ring

/-- The denominator consists of the original action normalizers and
factorials of the original occurrence counts. -/
theorem assembledOrbitProfile_card_le_rat {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {P : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → Prop}
    (hnatural : OrbitProfileFamilyNatural Ω m U P) :
    (Nat.card (AssembledOrbitProfile P) : ℚ) ≤
      ((∑ i, m i * Fintype.card (Ω i)).factorial : ℚ) * Nat.card {K // P K} /
        (∏ i, (Nat.card (Subgroup.normalizer (U i : Set (Equiv.Perm (Ω i)))) : ℚ) ^ m i *
          (m i).factorial) := by
  have h : (Nat.card (AssembledOrbitProfile P) : ℚ) ≤
      Nat.card (LabelledOrbitAtlas Ω m U) * Nat.card {K // P K} := by
    exact_mod_cast assembledOrbitProfile_card_le hnatural
  rw [labelledOrbitAtlas_card_rat Ω m U] at h
  convert h using 1 <;> ring

/-- The same upper bound on any physically labelled set of the same size. -/
theorem assembledOrbitProfileOn_card_le {ι X : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {P : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → Prop}
    (hnatural : OrbitProfileFamilyNatural Ω m U P) (e : OrbitProfilePoints Ω m ≃ X) :
    Nat.card (AssembledOrbitProfileOn P X) ≤
      Nat.card (LabelledOrbitAtlas Ω m U) * Nat.card {K // P K} := by
  rw [← Nat.card_congr (assembledOrbitProfileEquivOn P e)]
  exact assembledOrbitProfile_card_le hnatural

end SymmetricSubgroupAsymptotics
