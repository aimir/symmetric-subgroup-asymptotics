import SymmetricSubgroupAsymptotics.Statements

/-!
# Labelled profiles of permutation actions

Internal changes of block coordinates use the normalizers in the original
permutation groups. Different action colours are separate even if their
underlying sets have equal cardinality.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

/-- The labelled model set has a colour, an occurrence, and an actual local point. -/
abbrev OrbitProfilePoints {ι : Type*} (Ω : ι → Type*) (m : ι → ℕ) :=
  Σ i, Fin (m i) × Ω i

/-- Concrete internal reparametrizations: a permutation of equal-colour
occurrences and one original-action normalizer on every occurrence. -/
abbrev OrbitProfileCoordinates {ι : Type*} (Ω : ι → Type*) (m : ι → ℕ)
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) :=
  (∀ i, Equiv.Perm (Fin (m i))) ×
    (∀ i, Fin (m i) → Subgroup.normalizer (U i : Set (Equiv.Perm (Ω i))))

/-- The literal permutation induced by the chosen internal coordinates. -/
def orbitProfileCoordinatePerm {ι : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))} (c : OrbitProfileCoordinates Ω m U) :
    Equiv.Perm (OrbitProfilePoints Ω m) where
  toFun z := ⟨z.1, c.1 z.1 z.2.1, (c.2 z.1 z.2.1 : Equiv.Perm (Ω z.1)) z.2.2⟩
  invFun z := ⟨z.1, (c.1 z.1).symm z.2.1,
    (c.2 z.1 ((c.1 z.1).symm z.2.1) : Equiv.Perm (Ω z.1)).symm z.2.2⟩
  left_inv z := by rcases z with ⟨i,j,x⟩; simp
  right_inv z := by rcases z with ⟨i,j,x⟩; simp

theorem orbitProfileCoordinatePerm_injective {ι : Type*} {Ω : ι → Type*}
    [∀ i, Nonempty (Ω i)] {m : ι → ℕ} {U : ∀ i, Subgroup (Equiv.Perm (Ω i))} :
    Function.Injective (@orbitProfileCoordinatePerm ι Ω m U) := by
  intro c d h
  apply Prod.ext
  · funext i
    apply Equiv.ext
    intro j
    have he := Equiv.congr_fun h ⟨i,j,Classical.choice (inferInstance : Nonempty (Ω i))⟩
    have hp : (c.1 i j, (c.2 i j : Equiv.Perm (Ω i)) (Classical.choice (inferInstance : Nonempty (Ω i)))) =
        (d.1 i j, (d.2 i j : Equiv.Perm (Ω i)) (Classical.choice (inferInstance : Nonempty (Ω i)))) := by
      simpa only [orbitProfileCoordinatePerm, Equiv.coe_fn_mk, Sigma.mk.inj_iff, heq_eq_eq, true_and] using he
    exact congrArg Prod.fst hp
  · funext i j
    apply Subtype.ext
    apply Equiv.ext
    intro x
    have he := Equiv.congr_fun h ⟨i,j,x⟩
    have hp : (c.1 i j, (c.2 i j : Equiv.Perm (Ω i)) x) =
        (d.1 i j, (d.2 i j : Equiv.Perm (Ω i)) x) := by
      simpa only [orbitProfileCoordinatePerm, Equiv.coe_fn_mk, Sigma.mk.inj_iff, heq_eq_eq, true_and] using he
    exact congrArg Prod.snd hp

/-- The internal symmetry subgroup is specified by actual block permutations,
not by its desired cardinality. -/
def orbitProfileSymmetries {ι : Type*} (Ω : ι → Type*) (m : ι → ℕ)
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) where
  carrier := Set.range (@orbitProfileCoordinatePerm ι Ω m U)
  one_mem' := by
    refine ⟨⟨fun _ ↦ 1, fun _ _ ↦ 1⟩, ?_⟩
    apply Equiv.ext
    rintro ⟨i,j,x⟩
    rfl
  mul_mem' := by
    rintro a b ⟨c,rfl⟩ ⟨d,rfl⟩
    refine ⟨⟨fun i ↦ c.1 i * d.1 i,
      fun i j ↦ c.2 i (d.1 i j) * d.2 i j⟩, ?_⟩
    apply Equiv.ext
    rintro ⟨i,j,x⟩
    rfl
  inv_mem' := by
    rintro a ⟨c,rfl⟩
    refine ⟨⟨fun i ↦ (c.1 i)⁻¹, fun i j ↦ (c.2 i ((c.1 i)⁻¹ j))⁻¹⟩, ?_⟩
    apply Equiv.ext
    rintro ⟨i,j,x⟩
    rfl

/-- Every internal symmetry has unique occurrence and normalizer coordinates. -/
def orbitProfileSymmetriesEquiv {ι : Type*} (Ω : ι → Type*)
    [∀ i, Nonempty (Ω i)] (m : ι → ℕ) (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) :
    OrbitProfileCoordinates Ω m U ≃ orbitProfileSymmetries Ω m U :=
  Equiv.ofInjective _ orbitProfileCoordinatePerm_injective

theorem orbitProfileSymmetries_card {ι : Type*} [Fintype ι] (Ω : ι → Type*)
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    (m : ι → ℕ) (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) :
    Nat.card (orbitProfileSymmetries Ω m U) =
      ∏ i, (Nat.card (Subgroup.normalizer (U i : Set (Equiv.Perm (Ω i))))) ^ m i *
        (m i).factorial := by
  classical
  rw [← Nat.card_congr (orbitProfileSymmetriesEquiv Ω m U)]
  simp only [OrbitProfileCoordinates, Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_pi, Fintype.card_perm, Fintype.card_fin]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

/-- A labelled profile is a labelling of the concrete block model, with only
internal block coordinates and occurrence names forgotten. -/
abbrev LabelledOrbitProfile {ι : Type*} (Ω : ι → Type*) (m : ι → ℕ)
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) :=
  Equiv.Perm (OrbitProfilePoints Ω m) ⧸ orbitProfileSymmetries Ω m U

/-- The exact integer count of labelled profiles. The denominator is proved
from the unique internal coordinates; equal-size colours remain separate. -/
theorem labelledOrbitProfile_card {ι : Type*} [Fintype ι] (Ω : ι → Type*)
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    (m : ι → ℕ) (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) :
    Nat.card (LabelledOrbitProfile Ω m U) =
      (∑ i, m i * Fintype.card (Ω i)).factorial /
        (∏ i, Nat.card (Subgroup.normalizer (U i : Set (Equiv.Perm (Ω i)))) ^ m i *
          (m i).factorial) := by
  classical
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (orbitProfileSymmetries Ω m U)
  have hpos : 0 < Nat.card (orbitProfileSymmetries Ω m U) := Nat.card_pos
  have hp : Nat.card (Equiv.Perm (OrbitProfilePoints Ω m)) =
      (∑ i, m i * Fintype.card (Ω i)).factorial := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, OrbitProfilePoints,
      Fintype.card_sigma, Fintype.card_prod]
  change Nat.card (Equiv.Perm (OrbitProfilePoints Ω m) ⧸ orbitProfileSymmetries Ω m U) = _
  rw [hp, orbitProfileSymmetries_card Ω m U] at h
  rw [h, Nat.mul_div_cancel]
  simpa only [orbitProfileSymmetries_card Ω m U] using hpos

/-- A local test for being an internal symmetry. Bijectivity of the occurrence
map follows from the ambient permutation and nonempty local blocks. -/
theorem mem_orbitProfileSymmetries_iff {ι : Type*} {Ω : ι → Type*}
    [∀ i, Nonempty (Ω i)] {m : ι → ℕ} {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    (g : Equiv.Perm (OrbitProfilePoints Ω m)) :
    g ∈ orbitProfileSymmetries Ω m U ↔
      ∀ i (j : Fin (m i)), ∃ k : Fin (m i),
        ∃ a : Subgroup.normalizer (U i : Set (Equiv.Perm (Ω i))),
          ∀ x, g ⟨i,j,x⟩ = ⟨i,k,(a : Equiv.Perm (Ω i)) x⟩ := by
  classical
  constructor
  · rintro ⟨c,rfl⟩ i j
    exact ⟨c.1 i j,c.2 i j,fun _ ↦ rfl⟩
  · intro h
    choose k a ha using h
    have hk (i : ι) : Function.Injective (k i) := by
      intro j l hjl
      let x : Ω i := Classical.choice (inferInstance : Nonempty (Ω i))
      let y := (a i l : Equiv.Perm (Ω i)).symm ((a i j : Equiv.Perm (Ω i)) x)
      have he : g ⟨i,j,x⟩ = g ⟨i,l,y⟩ := by
        rw [ha,ha,hjl]
        simp [y]
      have he' := g.injective he
      have hp : (j,x) = (l,y) := by simpa using he'
      exact congrArg Prod.fst hp
    let p : ∀ i, Equiv.Perm (Fin (m i)) := fun i ↦
      Equiv.ofBijective (k i) ⟨hk i,Finite.surjective_of_injective (hk i)⟩
    refine ⟨⟨p,a⟩,?_⟩
    apply Equiv.ext
    rintro ⟨i,j,x⟩
    exact (ha i j x).symm

/-- All admissible charts of each actual labelled block. An occurrence name
is forgotten, and chart changes are exactly original-action normalizers. -/
def orbitProfileAtlas {ι : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i)))
    (g : Equiv.Perm (OrbitProfilePoints Ω m)) : ∀ i, Set (Ω i → OrbitProfilePoints Ω m) :=
  fun i ↦ {e | ∃ j : Fin (m i),
    ∃ a : Subgroup.normalizer (U i : Set (Equiv.Perm (Ω i))),
      e = fun x ↦ g ⟨i,j,(a : Equiv.Perm (Ω i)) x⟩}

private theorem atlas_subset_of_internal {ι : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    (g h : Equiv.Perm (OrbitProfilePoints Ω m))
    (hh : g⁻¹*h ∈ orbitProfileSymmetries Ω m U) (i : ι) :
    orbitProfileAtlas U h i ⊆ orbitProfileAtlas U g i := by
  obtain ⟨c,hc⟩ := hh
  have hperm : h = g*orbitProfileCoordinatePerm c := by rw [hc]; group
  rintro e ⟨j,a,rfl⟩
  refine ⟨c.1 i j,c.2 i j*a,?_⟩
  funext x
  rw [hperm]
  rfl

/-- Equality of literal chart families has exactly the internal-symmetry
fibres. Thus the finite quotient introduces neither extra nor missing data. -/
theorem orbitProfileAtlas_eq_iff {ι : Type*} {Ω : ι → Type*}
    [∀ i, Nonempty (Ω i)] {m : ι → ℕ} {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    (g h : Equiv.Perm (OrbitProfilePoints Ω m)) :
    orbitProfileAtlas U g = orbitProfileAtlas U h ↔
      g⁻¹*h ∈ orbitProfileSymmetries Ω m U := by
  constructor
  · intro he
    apply (mem_orbitProfileSymmetries_iff _).mpr
    intro i j
    have hm : (fun x ↦ h ⟨i,j,x⟩) ∈ orbitProfileAtlas U h i := ⟨j,1,rfl⟩
    rw [← he] at hm
    obtain ⟨k,a,ha⟩ := hm
    refine ⟨k,a,?_⟩
    intro x
    have hax := congrFun ha x
    change g.symm (h ⟨i,j,x⟩) = _
    rw [hax]
    simp
  · intro hh
    have hh' : h⁻¹*g ∈ orbitProfileSymmetries Ω m U := by
      simpa using (orbitProfileSymmetries Ω m U).inv_mem hh
    funext i
    exact Set.Subset.antisymm (atlas_subset_of_internal h g hh' i)
      (atlas_subset_of_internal g h hh i)

/-- Actual families of block charts obtainable on the labelled model set.
This is a subtype of concrete finite data, not a prescribed cardinality. -/
def LabelledOrbitAtlas {ι : Type*} (Ω : ι → Type*) (m : ι → ℕ)
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) :=
  Set.range (@orbitProfileAtlas ι Ω m U)

/-- Forgetting the internal frame names gives precisely the concrete atlas. -/
def labelledOrbitProfileEquivAtlas {ι : Type*} (Ω : ι → Type*)
    [∀ i, Nonempty (Ω i)] (m : ι → ℕ) (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) :
    LabelledOrbitProfile Ω m U ≃ LabelledOrbitAtlas Ω m U :=
  (Quotient.congrRight fun g h ↦ by
    rw [QuotientGroup.leftRel_apply]
    change g⁻¹*h ∈ orbitProfileSymmetries Ω m U ↔ orbitProfileAtlas U g = orbitProfileAtlas U h
    exact (orbitProfileAtlas_eq_iff g h).symm).trans (Setoid.quotientKerEquivRange _)

/-- Exact count of the concrete labelled block-atlas data. -/
theorem labelledOrbitAtlas_card {ι : Type*} [Fintype ι] (Ω : ι → Type*)
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    (m : ι → ℕ) (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) :
    Nat.card (LabelledOrbitAtlas Ω m U) =
      (∑ i, m i * Fintype.card (Ω i)).factorial /
        (∏ i, Nat.card (Subgroup.normalizer (U i : Set (Equiv.Perm (Ω i)))) ^ m i *
          (m i).factorial) := by
  rw [← Nat.card_congr (labelledOrbitProfileEquivAtlas Ω m U)]
  exact labelledOrbitProfile_card Ω m U

/-- A literal subgroup has the prescribed full coordinate projections after
labelling by `g`. Both preservation and surjectivity concern actual elements. -/
structure OrbitProfileFull {ι : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) (g : Equiv.Perm (OrbitProfilePoints Ω m))
    (H : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m))) : Prop where
  maps : ∀ h : H, ∀ i (j : Fin (m i)), ∃ u : U i,
    ∀ x, (h : Equiv.Perm (OrbitProfilePoints Ω m)) (g ⟨i,j,x⟩) =
      g ⟨i,j,(u : Equiv.Perm (Ω i)) x⟩
  full : ∀ i (j : Fin (m i)) (u : U i), ∃ h : H,
    ∀ x, (h : Equiv.Perm (OrbitProfilePoints Ω m)) (g ⟨i,j,x⟩) =
      g ⟨i,j,(u : Equiv.Perm (Ω i)) x⟩

/-- Full subgroups recover their actual orbit blocks, using transitivity
of the specified actions rather than a declared partition. -/
theorem OrbitProfileFull.orbit_eq_block {ι : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))} {g : Equiv.Perm (OrbitProfilePoints Ω m)}
    {H : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m))} (hH : OrbitProfileFull U g H)
    (htrans : ∀ i (x y : Ω i), ∃ u : U i, (u : Equiv.Perm (Ω i)) x = y)
    (i : ι) (j : Fin (m i)) (x : Ω i) :
    MulAction.orbit H (g ⟨i,j,x⟩) = Set.range (fun y : Ω i ↦ g ⟨i,j,y⟩) := by
  ext z
  constructor
  · rintro ⟨h,rfl⟩
    obtain ⟨u,hu⟩ := hH.maps h i j
    exact ⟨(u : Equiv.Perm (Ω i)) x,(hu x).symm⟩
  · rintro ⟨y,rfl⟩
    obtain ⟨u,hu⟩ := htrans i x y
    obtain ⟨h,hh⟩ := hH.full i j u
    refine ⟨h,?_⟩
    change (h : Equiv.Perm (OrbitProfilePoints Ω m)) (g ⟨i,j,x⟩) = _
    rw [hh,hu]

/-- The projected action recovered from the actual subgroup is exactly the
specified literal local subgroup, not its isomorphism or conjugacy class. -/
theorem OrbitProfileFull.projected_action {ι : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))} {g : Equiv.Perm (OrbitProfilePoints Ω m)}
    {H : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m))} (hH : OrbitProfileFull U g H)
    (i : ι) (j : Fin (m i)) :
    {u : Equiv.Perm (Ω i) | ∃ h : H, ∀ x,
      (h : Equiv.Perm (OrbitProfilePoints Ω m)) (g ⟨i,j,x⟩) = g ⟨i,j,u x⟩} = U i := by
  ext u
  constructor
  · rintro ⟨h,hu⟩
    obtain ⟨v,hv⟩ := hH.maps h i j
    have huv : u = (v : Equiv.Perm (Ω i)) := by
      apply Equiv.ext
      intro x
      have he := g.injective ((hu x).symm.trans (hv x))
      simpa using he
    rw [huv]
    exact v.property
  · intro hu
    exact hH.full i j ⟨u,hu⟩

private theorem full_transport_mem {ι : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))} {g h : Equiv.Perm (OrbitProfilePoints Ω m)}
    {H : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m))}
    (hg : OrbitProfileFull U g H) (hh : OrbitProfileFull U h H)
    {i l : ι} {j : Fin (m i)} {k : Fin (m l)} (e : Ω i ≃ Ω l)
    (he : ∀ x, h ⟨i,j,x⟩ = g ⟨l,k,e x⟩)
    (u : Equiv.Perm (Ω i)) (hu : u ∈ U i) : e.permCongr u ∈ U l := by
  obtain ⟨a,ha⟩ := hh.full i j ⟨u,hu⟩
  obtain ⟨v,hv⟩ := hg.maps a l k
  have hvu (x : Ω i) : (v : Equiv.Perm (Ω l)) (e x) = e (u x) := by
    have hax := ha x
    rw [he,he,hv] at hax
    simpa using g.injective hax
  have hev : e.permCongr u = (v : Equiv.Perm (Ω l)) := by
    apply Equiv.ext
    intro y
    simpa using (hvu (e.symm y)).symm
  rw [hev]
  exact v.property

private theorem profile_chart_injective {ι : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    (g : Equiv.Perm (OrbitProfilePoints Ω m)) (i : ι) (j : Fin (m i)) :
    Function.Injective (fun x : Ω i ↦ g ⟨i,j,x⟩) := by
  intro x y h
  simpa using g.injective h

/-- Pairwise distinction of actual permutation-action types. This keeps
same-degree actions separate without demanding different cardinalities. -/
def OrbitActionTypesSeparated {ι : Type*} (Ω : ι → Type*)
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) : Prop :=
  ∀ i l (e : Ω i ≃ Ω l),
    (∀ u ∈ U i, e.permCongr u ∈ U l) →
    (∀ v ∈ U l, e.symm.permCongr v ∈ U i) → i=l

/-- A subgroup full on the specified transitive actions determines its whole
labelled atlas. Hence different atlas data cannot count the same subgroup. -/
theorem OrbitProfileFull.atlas_unique {ι : Type*} {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))} {g h : Equiv.Perm (OrbitProfilePoints Ω m)}
    {H : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m))}
    (hg : OrbitProfileFull U g H) (hh : OrbitProfileFull U h H)
    (htrans : ∀ i (x y : Ω i), ∃ u : U i, (u : Equiv.Perm (Ω i)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U) : orbitProfileAtlas U g = orbitProfileAtlas U h := by
  classical
  apply (orbitProfileAtlas_eq_iff g h).mpr
  apply (mem_orbitProfileSymmetries_iff _).mpr
  intro i j
  let x0 : Ω i := Classical.choice (inferInstance : Nonempty (Ω i))
  let z := g.symm (h ⟨i,j,x0⟩)
  obtain ⟨l,k,y,hpoint⟩ : ∃ (l : ι) (k : Fin (m l)) (y : Ω l), h ⟨i,j,x0⟩ = g ⟨l,k,y⟩ := by
    exact ⟨z.1,z.2.1,z.2.2,(g.apply_symm_apply _).symm⟩
  have hblocks : Set.range (fun x : Ω i ↦ h ⟨i,j,x⟩) =
      Set.range (fun y : Ω l ↦ g ⟨l,k,y⟩) := by
    rw [← hh.orbit_eq_block htrans i j x0, ← hg.orbit_eq_block htrans l k y,hpoint]
  let eh := Equiv.ofInjective (fun x : Ω i ↦ h ⟨i,j,x⟩) (profile_chart_injective h i j)
  let eg := Equiv.ofInjective (fun y : Ω l ↦ g ⟨l,k,y⟩) (profile_chart_injective g l k)
  let e : Ω i ≃ Ω l := (eh.trans (Equiv.setCongr hblocks)).trans eg.symm
  have he (x : Ω i) : h ⟨i,j,x⟩ = g ⟨l,k,e x⟩ := by
    have hc := congrArg Subtype.val (eg.apply_symm_apply ((Equiv.setCongr hblocks) (eh x)))
    exact hc.symm
  have he' (y : Ω l) : g ⟨l,k,y⟩ = h ⟨i,j,e.symm y⟩ := by
    simpa using (he (e.symm y)).symm
  have hil : i=l := hsep i l e (full_transport_mem hg hh e he)
    (full_transport_mem hh hg e.symm he')
  subst l
  have hen : e ∈ Subgroup.normalizer (U i : Set (Equiv.Perm (Ω i))) := by
    apply Subgroup.mem_normalizer_fintype
    intro u hu
    have hmem := full_transport_mem hg hh e he u hu
    convert hmem using 1
  refine ⟨k,⟨e,hen⟩,?_⟩
  intro x
  change g.symm (h ⟨i,j,x⟩) = _
  rw [he]
  simp

/-- The original profile weight as an exact rational identity, with no
truncation from natural-number division. -/
theorem labelledOrbitAtlas_card_rat {ι : Type*} [Fintype ι] (Ω : ι → Type*)
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    (m : ι → ℕ) (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) :
    (Nat.card (LabelledOrbitAtlas Ω m U) : ℚ) =
      ((∑ i, m i * Fintype.card (Ω i)).factorial : ℚ) /
        (∏ i, (Nat.card (Subgroup.normalizer (U i : Set (Equiv.Perm (Ω i)))) : ℚ) ^ m i *
          (m i).factorial) := by
  classical
  have hp : Nat.card (Equiv.Perm (OrbitProfilePoints Ω m)) =
      (∑ i, m i * Fintype.card (Ω i)).factorial := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, OrbitProfilePoints,
      Fintype.card_sigma, Fintype.card_prod]
  have hd := Subgroup.card_subgroup_dvd_card (orbitProfileSymmetries Ω m U)
  rw [orbitProfileSymmetries_card Ω m U,hp] at hd
  have hpos : (0:ℚ) < Nat.card (orbitProfileSymmetries Ω m U) :=
    by exact_mod_cast (Nat.card_pos : 0 < Nat.card (orbitProfileSymmetries Ω m U))
  have hden : ((∏ i, Nat.card (Subgroup.normalizer (U i : Set (Equiv.Perm (Ω i)))) ^ m i *
      (m i).factorial : ℕ) : ℚ) ≠ 0 := by
    rw [← orbitProfileSymmetries_card Ω m U]
    exact hpos.ne'
  rw [labelledOrbitAtlas_card Ω m U,Nat.cast_div hd hden]
  push_cast
  rfl

end SymmetricSubgroupAsymptotics
