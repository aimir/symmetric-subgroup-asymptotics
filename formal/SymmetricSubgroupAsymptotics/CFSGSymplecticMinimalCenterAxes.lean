import SymmetricSubgroupAsymptotics.CFSGSymplecticBorelCenterAxes

/-! The only nontrivial minimal B-normalized subgroups of the actual
characteristic-two unipotent centre are its two literal axes, for q>2.
Minimality here quantifies over the actual ambient subgroups and their
same B-normalizers; it is not a representation-classification premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem longCenterAxis_le_range (r : ℕ) (hr : 0 < r) :
    longCenterAxis (K := K) r hr ≤ (centerToElementary r hr).range := by
  rintro x ⟨y, _, rfl⟩
  exact ⟨y, rfl⟩

omit [Finite K] in
theorem shortCenterAxis_le_range (r : ℕ) (hr : 0 < r) :
    shortCenterAxis (K := K) r hr ≤ (centerToElementary r hr).range := by
  rintro x ⟨y, _, rfl⟩
  exact ⟨y, rfl⟩

theorem shortCenterAxis_not_le_long (r : ℕ) (hr : 0 < r) :
    ¬ shortCenterAxis (K := K) r hr ≤ longCenterAxis r hr := by
  intro h
  apply shortCenterAxis_ne_bot (K := K) r hr
  calc
    shortCenterAxis r hr = longCenterAxis r hr ⊓ shortCenterAxis r hr := (inf_of_le_right h).symm
    _ = ⊥ := disjoint_iff.mp (centerAxes_disjoint r hr)

theorem longCenterAxis_not_le_short (r : ℕ) (hr : 0 < r) :
    ¬ longCenterAxis (K := K) r hr ≤ shortCenterAxis r hr := by
  intro h
  apply longCenterAxis_ne_bot (K := K) r hr
  calc
    longCenterAxis r hr = longCenterAxis r hr ⊓ shortCenterAxis r hr := (inf_of_le_left h).symm
    _ = ⊥ := disjoint_iff.mp (centerAxes_disjoint r hr)

theorem minimal_normalized_center_subgroup_axis (r : ℕ) (hr : 0 < r)
    (hq : 2 < Nat.card K) (H : Subgroup (elementaryRootGroup K (r + 1)))
    (hne : H ≠ ⊥) (hZ : H ≤ (centerToElementary (K := K) r hr).range)
    (hN : borel K (r + 1) ≤ Subgroup.normalizer (H : Set (elementaryRootGroup K (r + 1))))
    (hmin : ∀ J : Subgroup (elementaryRootGroup K (r + 1)),
      J ≠ ⊥ → J ≤ H →
      borel K (r + 1) ≤ Subgroup.normalizer (J : Set (elementaryRootGroup K (r + 1))) → J = H) :
    H = longCenterAxis r hr ∨ H = shortCenterAxis r hr := by
  rcases normalized_center_subgroup_four_cases r hr hq H hN hZ with h | h | h | h
  · exact False.elim (hne h)
  · exact Or.inl h
  · exact Or.inr h
  · have hL : longCenterAxis r hr = H := hmin _ (longCenterAxis_ne_bot r hr)
      ((longCenterAxis_le_range r hr).trans_eq h.symm) (borel_le_normalizer_longCenterAxis r hr)
    have hR : shortCenterAxis r hr ≤ longCenterAxis r hr :=
      (shortCenterAxis_le_range r hr).trans_eq (h.symm.trans hL.symm)
    exact False.elim (shortCenterAxis_not_le_long r hr hR)

theorem longCenterAxis_minimal (r : ℕ) (hr : 0 < r) (hq : 2 < Nat.card K)
    (H : Subgroup (elementaryRootGroup K (r + 1)))
    (hne : H ≠ ⊥) (hH : H ≤ longCenterAxis r hr)
    (hN : borel K (r + 1) ≤ Subgroup.normalizer (H : Set (elementaryRootGroup K (r + 1)))) :
    H = longCenterAxis r hr := by
  rcases normalized_center_subgroup_four_cases r hr hq H hN
    (hH.trans (longCenterAxis_le_range r hr)) with h | h | h | h
  · exact False.elim (hne h)
  · exact h
  · exact False.elim (shortCenterAxis_not_le_long r hr (h ▸ hH))
  · have hrange : (centerToElementary (K := K) r hr).range ≤ longCenterAxis r hr := h ▸ hH
    exact False.elim (shortCenterAxis_not_le_long r hr ((shortCenterAxis_le_range r hr).trans hrange))

theorem shortCenterAxis_minimal (r : ℕ) (hr : 0 < r) (hq : 2 < Nat.card K)
    (H : Subgroup (elementaryRootGroup K (r + 1)))
    (hne : H ≠ ⊥) (hH : H ≤ shortCenterAxis r hr)
    (hN : borel K (r + 1) ≤ Subgroup.normalizer (H : Set (elementaryRootGroup K (r + 1)))) :
    H = shortCenterAxis r hr := by
  rcases normalized_center_subgroup_four_cases r hr hq H hN
    (hH.trans (shortCenterAxis_le_range r hr)) with h | h | h | h
  · exact False.elim (hne h)
  · exact False.elim (longCenterAxis_not_le_short r hr (h ▸ hH))
  · exact h
  · have hrange : (centerToElementary (K := K) r hr).range ≤ shortCenterAxis r hr := h ▸ hH
    exact False.elim (longCenterAxis_not_le_short r hr ((longCenterAxis_le_range r hr).trans hrange))

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
