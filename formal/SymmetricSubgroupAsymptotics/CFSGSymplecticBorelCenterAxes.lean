import SymmetricSubgroupAsymptotics.CFSGSymplecticBorelCenterFourCases

/-! The two actual centre axes are nontrivial, disjoint, and
normalized by the SAME original Borel. These facts make the four-case
calculation available to intrinsic minimal-normal subgroup arguments. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices CFSGTwoWeightAdditiveSubgroups
variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem centerToElementary_injective (r : ℕ) (hr : 0 < r) :
    Function.Injective (centerToElementary (K := K) r hr) := by
  intro x y h
  apply centerParameterHom_injective r hr
  apply Subtype.ext
  apply Subtype.ext
  exact h

omit [Finite K] in
theorem mem_longCenterAxis_iff (r : ℕ) (hr : 0 < r)
    (g : elementaryRootGroup K (r + 1)) :
    g ∈ longCenterAxis r hr ↔ ∃ a : K, g = (centerParameterElement r hr a 0).val := by
  constructor
  · rintro ⟨x, hx, hxe⟩
    have hx0 : x.toAdd.2 = 0 := hx.2
    refine ⟨x.toAdd.1, ?_⟩
    calc
      g = centerToElementary r hr x := hxe.symm
      _ = _ := by change (centerParameterElement r hr x.toAdd.1 x.toAdd.2).val = _; rw [hx0]
  · rintro ⟨a, ha⟩
    exact ⟨Multiplicative.ofAdd (a, 0), ⟨AddSubgroup.mem_top _, rfl⟩, ha.symm⟩

omit [Finite K] in
theorem mem_shortCenterAxis_iff (r : ℕ) (hr : 0 < r)
    (g : elementaryRootGroup K (r + 1)) :
    g ∈ shortCenterAxis r hr ↔ ∃ b : K, g = (centerParameterElement r hr 0 b).val := by
  constructor
  · rintro ⟨x, hx, hxe⟩
    have hx0 : x.toAdd.1 = 0 := hx.1
    refine ⟨x.toAdd.2, ?_⟩
    calc
      g = centerToElementary r hr x := hxe.symm
      _ = _ := by change (centerParameterElement r hr x.toAdd.1 x.toAdd.2).val = _; rw [hx0]
  · rintro ⟨b, hb⟩
    exact ⟨Multiplicative.ofAdd (0, b), ⟨rfl, AddSubgroup.mem_top _⟩, hb.symm⟩

theorem borel_le_normalizer_longCenterAxis (r : ℕ) (hr : 0 < r) :
    borel K (r + 1) ≤ Subgroup.normalizer
      (longCenterAxis (K := K) r hr : Set (elementaryRootGroup K (r + 1))) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨a, rfl⟩ := (mem_longCenterAxis_iff r hr x).mp hx
  let b : borel K (r + 1) := ⟨g, hg⟩
  have he := borel_centerParameter_conjugation r hr b a 0
  apply (mem_longCenterAxis_iff r hr _).mpr
  refine ⟨a * ((b.val.val : Mat K (r + 1)) (Sum.inl 0) (Sum.inl 0)) ^ 2, ?_⟩
  simpa only [zero_mul] using he

theorem borel_le_normalizer_shortCenterAxis (r : ℕ) (hr : 0 < r) :
    borel K (r + 1) ≤ Subgroup.normalizer
      (shortCenterAxis (K := K) r hr : Set (elementaryRootGroup K (r + 1))) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨c, rfl⟩ := (mem_shortCenterAxis_iff r hr x).mp hx
  let b : borel K (r + 1) := ⟨g, hg⟩
  have he := borel_centerParameter_conjugation r hr b 0 c
  dsimp only at he
  apply (mem_shortCenterAxis_iff r hr _).mpr
  refine ⟨c * ((b.val.val : Mat K (r + 1)) (Sum.inl 0) (Sum.inl 0)) *
    ((b.val.val : Mat K (r + 1)) (Sum.inl (⟨1, by omega⟩ : Fin (r + 1)))
      (Sum.inl (⟨1, by omega⟩ : Fin (r + 1)))), ?_⟩
  simpa only [zero_mul, b] using he

omit [Finite K] in
theorem centerAxes_disjoint (r : ℕ) (hr : 0 < r) :
    Disjoint (longCenterAxis (K := K) r hr) (shortCenterAxis r hr) := by
  apply disjoint_iff.mpr
  apply le_antisymm ?_ bot_le
  intro g hg
  obtain ⟨a, ha⟩ := (mem_longCenterAxis_iff r hr g).mp hg.1
  obtain ⟨b, hb⟩ := (mem_shortCenterAxis_iff r hr g).mp hg.2
  have he : centerToElementary r hr (Multiplicative.ofAdd (a, 0)) =
      centerToElementary r hr (Multiplicative.ofAdd (0, b)) := ha.symm.trans hb
  have hp := centerToElementary_injective r hr he
  have ha0 : a = 0 := congrArg (fun x : Multiplicative (K × K) => x.toAdd.1) hp
  change g = 1
  calc
    g = centerToElementary r hr (Multiplicative.ofAdd (a, 0)) := ha
    _ = centerToElementary r hr 1 := by rw [ha0]; rfl
    _ = 1 := map_one _

omit [Finite K] in
theorem longCenterAxis_ne_bot (r : ℕ) (hr : 0 < r) :
    longCenterAxis (K := K) r hr ≠ ⊥ := by
  intro h
  have hx : centerToElementary r hr (Multiplicative.ofAdd ((1 : K), 0)) ∈ longCenterAxis r hr :=
    (mem_longCenterAxis_iff r hr _).mpr ⟨1, rfl⟩
  rw [h] at hx
  have he := centerToElementary_injective r hr (show
    centerToElementary r hr (Multiplicative.ofAdd ((1 : K), 0)) = centerToElementary r hr 1 from
      hx.trans (map_one _).symm)
  exact one_ne_zero (congrArg (fun x : Multiplicative (K × K) => x.toAdd.1) he)

omit [Finite K] in
theorem shortCenterAxis_ne_bot (r : ℕ) (hr : 0 < r) :
    shortCenterAxis (K := K) r hr ≠ ⊥ := by
  intro h
  have hx : centerToElementary r hr (Multiplicative.ofAdd (0, (1 : K))) ∈ shortCenterAxis r hr :=
    (mem_shortCenterAxis_iff r hr _).mpr ⟨1, rfl⟩
  rw [h] at hx
  have he := centerToElementary_injective r hr (show
    centerToElementary r hr (Multiplicative.ofAdd (0, (1 : K))) = centerToElementary r hr 1 from
      hx.trans (map_one _).symm)
  exact one_ne_zero (congrArg (fun x : Multiplicative (K × K) => x.toAdd.2) he)

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
