import SymmetricSubgroupAsymptotics.CFSGSymplecticBorelCenterSubgroups
import Mathlib.SetTheory.Cardinal.Finite

/-! Over a characteristic-two field with more than two elements,
every actual B-normalized subgroup contained in the actual unipotent
centre is zero, one of its two coordinate root groups, or the full
centre. No witness unit remains in this concrete statement. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices CFSGTwoWeightAdditiveSubgroups
variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
private theorem exists_unit_ne_one (hq : 2 < Nat.card K) : ∃ u : Kˣ, (u : K) ≠ 1 := by
  letI centerFourCases_fintype : Fintype K := Fintype.ofFinite K
  have hc : 3 ≤ Fintype.card K := by
    rw [← Nat.card_eq_fintype_card]
    omega
  have he : 3 ≤ ENat.card K := by
    rw [ENat.card_eq_coe_fintype_card]
    exact_mod_cast hc
  obtain ⟨a, ha0, ha1⟩ := ENat.exists_ne_ne_of_three_le he (0 : K) 1
  exact ⟨Units.mk0 a ha0, ha1⟩

def longCenterAxis (r : ℕ) (hr : 0 < r) : Subgroup (elementaryRootGroup K (r + 1)) :=
  (leftAxis (K := K)).toSubgroup.map (centerToElementary r hr)

def shortCenterAxis (r : ℕ) (hr : 0 < r) : Subgroup (elementaryRootGroup K (r + 1)) :=
  (rightAxis (K := K)).toSubgroup.map (centerToElementary r hr)

omit [Finite K] in
theorem centerToElementary_range (r : ℕ) (hr : 0 < r) :
    (centerToElementary (K := K) r hr).range =
      (Subgroup.center (unipotent K (r + 1))).map (unipotent K (r + 1)).subtype := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(centerParameterHom r hr x).val, (centerParameterHom r hr x).property, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨x, hx⟩ := centerParameterHom_surjective r hr ⟨u, hu⟩
    refine ⟨x, ?_⟩
    exact congrArg (fun z : Subgroup.center (unipotent K (r + 1)) => z.val.val) hx

theorem normalized_center_subgroup_four_cases (r : ℕ) (hr : 0 < r)
    (hq : 2 < Nat.card K) (H : Subgroup (elementaryRootGroup K (r + 1)))
    (hH : borel K (r + 1) ≤ Subgroup.normalizer (H : Set (elementaryRootGroup K (r + 1))))
    (hZ : H ≤ (centerToElementary (K := K) r hr).range) :
    H = ⊥ ∨ H = longCenterAxis r hr ∨ H = shortCenterAxis r hr ∨
      H = (centerToElementary (K := K) r hr).range := by
  obtain ⟨u, hu⟩ := exists_unit_ne_one hq
  have hcases := centerCoordinatePreimage_classification r hr H hH u hu
  have hmap (A : AddSubgroup (K × K)) (ha : centerCoordinatePreimage r hr H = A) :
      H = A.toSubgroup.map (centerToElementary r hr) := by
    have he := congrArg
      (fun P : AddSubgroup (K × K) => P.toSubgroup.map (centerToElementary r hr)) ha
    have hp : (centerCoordinatePreimage r hr H).toSubgroup = H.comap (centerToElementary r hr) :=
      AddSubgroup.toSubgroup.apply_symm_apply _
    dsimp only at he
    rw [hp, Subgroup.map_comap_eq_self hZ] at he
    exact he
  rcases hcases with h | h | h | h
  · left
    simpa only [map_bot, Subgroup.map_bot] using hmap ⊥ h
  · right; left
    exact hmap _ h
  · right; right; left
    exact hmap _ h
  · right; right; right
    have ht := hmap ⊤ h
    have he : (⊤ : AddSubgroup (K × K)).toSubgroup.map (centerToElementary r hr) =
        (centerToElementary (K := K) r hr).range := by
      change (⊤ : Subgroup (Multiplicative (K × K))).map (centerToElementary r hr) = _
      ext x
      constructor
      · rintro ⟨y, _, rfl⟩
        exact ⟨y, rfl⟩
      · rintro ⟨y, rfl⟩
        exact ⟨y, Subgroup.mem_top _, rfl⟩
    exact ht.trans he

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
