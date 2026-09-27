import SymmetricSubgroupAsymptotics.OrbitProfileAssembly

/-!
# Exact assembly with finite marks on actual subgroups

The original label fibre has the full original symmetry cardinality even
when an individual subgroup or mark is not fixed by that symmetry. A mark
that is natural under relabelling therefore assembles with the same original
normalizer and occurrence-factorial denominator as the unmarked family.
The statements concern actual subgroup sums, not counts of presentations.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics

local instance weightedAssemblySubgroupFinite (G : Type*) [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

private theorem weighted_sum_of_constant_fibres {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (c : ℕ) (hf : ∀ b, Nat.card {a // f a = b} = c) (w : B → ℕ) :
    (∑ a, w (f a)) = c * ∑ b, w b := by
  calc
    _ = ∑ z : Σ b : B, {a // f a = b}, w (f z.2.val) :=
      Fintype.sum_equiv (Equiv.sigmaFiberEquiv f).symm _ _ (fun _ => rfl)
    _ = ∑ z : Σ b : B, {a // f a = b}, w z.1 := by
      apply Finset.sum_congr rfl
      intro z _
      rw [z.2.property]
    _ = ∑ b : B, ∑ _a : {a // f a = b}, w b := Fintype.sum_sigma _
    _ = ∑ b : B, c * w b := by
      apply Finset.sum_congr rfl
      intro b _
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Nat.card_eq_fintype_card, hf]
      rfl
    _ = _ := (Finset.mul_sum _ _ _).symm

section Assembly

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {P : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → Prop}
    (hfull : ∀ K, P K → OrbitProfileFull U 1 K)
    (hnatural : OrbitProfileFamilyNatural Ω m U P)
    (htrans : ∀ i (x y : Ω i), ∃ u : U i, (u : Equiv.Perm (Ω i)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)

include hfull hnatural htrans hsep

/-- A relabelling-natural finite mark has the exact original atlas weight.
The mark may vary between actual subgroups in the same model family. -/
theorem assembledOrbitProfile_weighted_sum
    (w : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → ℕ)
    (hw : ∀ g K, w (relabelSubgroup g K) = w K) :
    (∑ H : AssembledOrbitProfile P, w H.val) =
      Nat.card (LabelledOrbitAtlas Ω m U) * ∑ K : {K // P K}, w K.val := by
  let f : Equiv.Perm (OrbitProfilePoints Ω m) × {K // P K} → AssembledOrbitProfile P :=
    fun p => ⟨orbitProfileLabelMap P p, ⟨p, rfl⟩⟩
  have hf (H : AssembledOrbitProfile P) :
      Nat.card {p // f p = H} = Nat.card (orbitProfileSymmetries Ω m U) := by
    obtain ⟨p, hp⟩ := H.property
    let e : {q // f q = H} ≃ {q // orbitProfileLabelMap P q = orbitProfileLabelMap P p} :=
      Equiv.subtypeEquivRight fun q => by
        change (⟨orbitProfileLabelMap P q, ⟨q, rfl⟩⟩ : AssembledOrbitProfile P) = H ↔ _
        rw [Subtype.ext_iff]
        exact Iff.intro (fun h => h.trans hp.symm) (fun h => h.trans hp)
    exact Nat.card_congr (e.trans (orbitProfileLabelFibreEquiv hfull hnatural htrans hsep p))
  have hc := weighted_sum_of_constant_fibres f _ hf (fun H => w H.val)
  have hg : Nat.card (Equiv.Perm (OrbitProfilePoints Ω m)) =
      Nat.card (LabelledOrbitAtlas Ω m U) * Nat.card (orbitProfileSymmetries Ω m U) := by
    rw [← Nat.card_congr (labelledOrbitProfileEquivAtlas Ω m U)]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup (orbitProfileSymmetries Ω m U)
  have hW : 0 < Nat.card (orbitProfileSymmetries Ω m U) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hW
  calc
    (∑ H : AssembledOrbitProfile P, w H.val) * Nat.card (orbitProfileSymmetries Ω m U) =
        ∑ p : Equiv.Perm (OrbitProfilePoints Ω m) × {K // P K}, w (f p).val := by
      simpa only [mul_comm] using hc.symm
    _ = Nat.card (Equiv.Perm (OrbitProfilePoints Ω m)) * ∑ K : {K // P K}, w K.val := by
      rw [Fintype.sum_prod_type]
      simp only [f, orbitProfileLabelMap, hw, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Nat.card_eq_fintype_card]
      rfl
    _ = (Nat.card (LabelledOrbitAtlas Ω m U) * ∑ K : {K // P K}, w K.val) *
        Nat.card (orbitProfileSymmetries Ω m U) := by rw [hg]; ring

/-- The mark can be a literal finite type attached to each original subgroup;
an actual relabelling equivalence supplies its cardinal naturality. -/
theorem assembledOrbitProfile_marked_card
    (Mark : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → Type*)
    [∀ H, Finite (Mark H)]
    (hmark : ∀ g K, Mark (relabelSubgroup g K) ≃ Mark K) :
    Nat.card (Σ H : AssembledOrbitProfile P, Mark H.val) =
      Nat.card (LabelledOrbitAtlas Ω m U) * Nat.card (Σ K : {K // P K}, Mark K.val) := by
  rw [Nat.card_sigma, Nat.card_sigma]
  exact assembledOrbitProfile_weighted_sum hfull hnatural htrans hsep
    (fun H => Nat.card (Mark H)) (fun g K => Nat.card_congr (hmark g K))

/-- Original internal normalizers and permutations of equal-action
occurrences remain in the denominator exactly once. -/
theorem assembledOrbitProfile_weighted_sum_rat
    (w : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → ℕ)
    (hw : ∀ g K, w (relabelSubgroup g K) = w K) :
    (∑ H : AssembledOrbitProfile P, (w H.val : ℚ)) =
      ((∑ i, m i * Fintype.card (Ω i)).factorial : ℚ) *
        (∑ K : {K // P K}, (w K.val : ℚ)) /
      (∏ i, (Nat.card (Subgroup.normalizer (U i : Set (Equiv.Perm (Ω i)))) : ℚ) ^ m i *
        (m i).factorial) := by
  have h := assembledOrbitProfile_weighted_sum hfull hnatural htrans hsep w hw
  have hq : (∑ H : AssembledOrbitProfile P, (w H.val : ℚ)) =
      (Nat.card (LabelledOrbitAtlas Ω m U) : ℚ) * ∑ K : {K // P K}, (w K.val : ℚ) := by
    exact_mod_cast h
  rw [hq, labelledOrbitAtlas_card_rat Ω m U]
  ring

end Assembly

end SymmetricSubgroupAsymptotics
