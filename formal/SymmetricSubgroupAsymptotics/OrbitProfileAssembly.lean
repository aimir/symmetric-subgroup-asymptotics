import SymmetricSubgroupAsymptotics.LabelledOrbitProfiles

/-!
# Assembly of full orbit profiles on an actual labelled set

Subgroups are transported by conjugation. Internal profile symmetries act on
both the labelling and the local subgroup; they need not fix individual lifts.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

/-- Relabel an actual permutation subgroup by an actual bijection of points. -/
def relabelSubgroup {X Y : Type*} (e : X ≃ Y) :
    Subgroup (Equiv.Perm X) ≃o Subgroup (Equiv.Perm Y) :=
  e.permCongrHom.mapSubgroup

@[simp] theorem mem_relabelSubgroup {X Y : Type*} (e : X ≃ Y)
    (H : Subgroup (Equiv.Perm X)) (p : Equiv.Perm Y) :
    p ∈ relabelSubgroup e H ↔ e.symm.permCongr p ∈ H :=
  Subgroup.mem_map_equiv

@[simp] theorem relabelSubgroup_refl {X : Type*} (H : Subgroup (Equiv.Perm X)) :
    relabelSubgroup (Equiv.refl X) H = H := by
  ext p
  rw [mem_relabelSubgroup]
  have he : (Equiv.refl X).symm.permCongr p = p := by
    apply Equiv.ext
    intro x
    rfl
  rw [he]

@[simp] theorem relabelSubgroup_trans {X Y Z : Type*} (e : X ≃ Y) (f : Y ≃ Z)
    (H : Subgroup (Equiv.Perm X)) :
    relabelSubgroup f (relabelSubgroup e H) = relabelSubgroup (e.trans f) H := by
  ext p
  simp only [mem_relabelSubgroup]
  rfl

@[simp] theorem relabelSubgroup_symm {X Y : Type*} (e : X ≃ Y)
    (H : Subgroup (Equiv.Perm X)) :
    relabelSubgroup e.symm (relabelSubgroup e H) = H := by
  rw [relabelSubgroup_trans, Equiv.self_trans_symm, relabelSubgroup_refl]

/-- Fullness on a common physical labelled set; different profiles may use
different model domains and multiplicities. -/
structure OrbitProfileFullOn {ι X : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) (e : OrbitProfilePoints Ω m ≃ X)
    (H : Subgroup (Equiv.Perm X)) : Prop where
  maps : ∀ h : H, ∀ i (j : Fin (m i)), ∃ u : U i,
    ∀ x, (h : Equiv.Perm X) (e ⟨i,j,x⟩) = e ⟨i,j,(u : Equiv.Perm (Ω i)) x⟩
  full : ∀ i (j : Fin (m i)) (u : U i), ∃ h : H,
    ∀ x, (h : Equiv.Perm X) (e ⟨i,j,x⟩) = e ⟨i,j,(u : Equiv.Perm (Ω i)) x⟩

theorem orbitProfileFullOn_iff {ι : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) (e : Equiv.Perm (OrbitProfilePoints Ω m))
    (H : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m))) :
    OrbitProfileFullOn U e H ↔ OrbitProfileFull U e H :=
  ⟨fun h ↦ ⟨h.maps,h.full⟩,fun h ↦ ⟨h.maps,h.full⟩⟩

/-- Full coordinate actions survive a change of the ambient point labels. -/
theorem OrbitProfileFullOn.relabel {ι X Y : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))} {e : OrbitProfilePoints Ω m ≃ X}
    {H : Subgroup (Equiv.Perm X)} (hH : OrbitProfileFullOn U e H) (f : X ≃ Y) :
    OrbitProfileFullOn U (e.trans f) (relabelSubgroup f H) := by
  constructor
  · intro h i j
    obtain ⟨u,hu⟩ := hH.maps ⟨f.symm.permCongr h,(mem_relabelSubgroup f H h).mp h.property⟩ i j
    refine ⟨u,fun x ↦ ?_⟩
    have hx := congrArg f (hu x)
    simpa using hx
  · intro i j u
    obtain ⟨h,hh⟩ := hH.full i j u
    refine ⟨⟨f.permCongr h,?_⟩,fun x ↦ ?_⟩
    · apply (mem_relabelSubgroup f H _).mpr
      have he : f.symm.permCongr (f.permCongr (h : Equiv.Perm X)) = h := by
        apply Equiv.ext
        intro x
        simp
      rw [he]
      exact h.property
    · simpa using congrArg f (hh x)

theorem OrbitProfileFull.relabel {ι : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {g : Equiv.Perm (OrbitProfilePoints Ω m)}
    {H : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m))}
    (hH : OrbitProfileFull U g H) (f : Equiv.Perm (OrbitProfilePoints Ω m)) :
    OrbitProfileFull U (f*g) (relabelSubgroup f H) :=
  (orbitProfileFullOn_iff _ _ _).mp
    ((orbitProfileFullOn_iff _ _ _).mpr hH |>.relabel f)

/-- The actual subgroup orbits recover the blocks even when the ambient
labelled set is different from the profile model. -/
theorem OrbitProfileFullOn.orbit_eq_block {ι X : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))} {e : OrbitProfilePoints Ω m ≃ X}
    {H : Subgroup (Equiv.Perm X)} (hH : OrbitProfileFullOn U e H)
    (htrans : ∀ i (x y : Ω i), ∃ u : U i, (u : Equiv.Perm (Ω i)) x = y)
    (i : ι) (j : Fin (m i)) (x : Ω i) :
    MulAction.orbit H (e ⟨i,j,x⟩) = Set.range (fun y : Ω i ↦ e ⟨i,j,y⟩) := by
  ext z
  constructor
  · rintro ⟨h,rfl⟩
    obtain ⟨u,hu⟩ := hH.maps h i j
    exact ⟨(u : Equiv.Perm (Ω i)) x,(hu x).symm⟩
  · rintro ⟨y,rfl⟩
    obtain ⟨u,hu⟩ := htrans i x y
    obtain ⟨h,hh⟩ := hH.full i j u
    refine ⟨h,?_⟩
    change (h : Equiv.Perm X) (e ⟨i,j,x⟩) = _
    rw [hh,hu]

private theorem fullOn_transport_mem {ι X : Type*} {Ω : ι → Type*} {m m' : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {g : OrbitProfilePoints Ω m ≃ X} {h : OrbitProfilePoints Ω m' ≃ X}
    {H : Subgroup (Equiv.Perm X)}
    (hg : OrbitProfileFullOn U g H) (hh : OrbitProfileFullOn U h H)
    {i l : ι} {j : Fin (m' i)} {k : Fin (m l)} (e : Ω i ≃ Ω l)
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

private theorem profileOn_chart_injective {ι X : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    (g : OrbitProfilePoints Ω m ≃ X) (i : ι) (j : Fin (m i)) :
    Function.Injective (fun x : Ω i ↦ g ⟨i,j,x⟩) := by
  intro x y h
  simpa using g.injective h

/-- A block in one full presentation matches a block of the same action
colour in every other presentation, even with different multiplicities. -/
theorem OrbitProfileFullOn.matching_block {ι X : Type*} {Ω : ι → Type*}
    [∀ i, Nonempty (Ω i)] {m m' : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {g : OrbitProfilePoints Ω m ≃ X} {h : OrbitProfilePoints Ω m' ≃ X}
    {H : Subgroup (Equiv.Perm X)}
    (hg : OrbitProfileFullOn U g H) (hh : OrbitProfileFullOn U h H)
    (htrans : ∀ i (x y : Ω i), ∃ u : U i, (u : Equiv.Perm (Ω i)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U) (i : ι) (j : Fin (m' i)) :
    ∃ k : Fin (m i), ∃ e : Equiv.Perm (Ω i), ∀ x, h ⟨i,j,x⟩ = g ⟨i,k,e x⟩ := by
  classical
  let x0 : Ω i := Classical.choice (inferInstance : Nonempty (Ω i))
  let z := g.symm (h ⟨i,j,x0⟩)
  obtain ⟨l,k,y,hpoint⟩ : ∃ (l : ι) (k : Fin (m l)) (y : Ω l),
      h ⟨i,j,x0⟩ = g ⟨l,k,y⟩ := by
    exact ⟨z.1,z.2.1,z.2.2,(g.apply_symm_apply _).symm⟩
  have hblocks : Set.range (fun x : Ω i ↦ h ⟨i,j,x⟩) =
      Set.range (fun y : Ω l ↦ g ⟨l,k,y⟩) := by
    rw [← hh.orbit_eq_block htrans i j x0, ← hg.orbit_eq_block htrans l k y,hpoint]
  let eh := Equiv.ofInjective (fun x : Ω i ↦ h ⟨i,j,x⟩) (profileOn_chart_injective h i j)
  let eg := Equiv.ofInjective (fun y : Ω l ↦ g ⟨l,k,y⟩) (profileOn_chart_injective g l k)
  let e : Ω i ≃ Ω l := (eh.trans (Equiv.setCongr hblocks)).trans eg.symm
  have he (x : Ω i) : h ⟨i,j,x⟩ = g ⟨l,k,e x⟩ := by
    exact (congrArg Subtype.val (eg.apply_symm_apply ((Equiv.setCongr hblocks) (eh x)))).symm
  have he' (y : Ω l) : g ⟨l,k,y⟩ = h ⟨i,j,e.symm y⟩ := by
    simpa using (he (e.symm y)).symm
  have hil : i=l := hsep i l e (fullOn_transport_mem hg hh e he)
    (fullOn_transport_mem hh hg e.symm he')
  subst l
  exact ⟨k,e,he⟩

/-- Multiplicities are invariants of the actual physical subgroup. This is
the disjointness input needed before summing different profile weights. -/
theorem OrbitProfileFullOn.multiplicity_unique {ι X : Type*} {Ω : ι → Type*}
    [∀ i, Nonempty (Ω i)] {m m' : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {g : OrbitProfilePoints Ω m ≃ X} {h : OrbitProfilePoints Ω m' ≃ X}
    {H : Subgroup (Equiv.Perm X)}
    (hg : OrbitProfileFullOn U g H) (hh : OrbitProfileFullOn U h H)
    (htrans : ∀ i (x y : Ω i), ∃ u : U i, (u : Equiv.Perm (Ω i)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U) : m = m' := by
  have hle {a b : ι → ℕ} {f : OrbitProfilePoints Ω a ≃ X}
      {f' : OrbitProfilePoints Ω b ≃ X} (hf : OrbitProfileFullOn U f H)
      (hf' : OrbitProfileFullOn U f' H) (i : ι) : b i ≤ a i := by
    classical
    choose k e he using fun j ↦ hf.matching_block hf' htrans hsep i j
    have hk : Function.Injective k := by
      intro j l hjl
      let x : Ω i := Classical.choice (inferInstance : Nonempty (Ω i))
      have hx : f' ⟨i,j,x⟩ = f' ⟨i,l,(e l).symm (e j x)⟩ := by
        rw [he,he,hjl]
        simp
      have hp : (j,x) = (l,(e l).symm (e j x)) := by simpa using f'.injective hx
      exact congrArg Prod.fst hp
    simpa using Fintype.card_le_of_injective k hk
  funext i
  exact Nat.le_antisymm (hle hh hg i) (hle hg hh i)

@[simp] theorem relabelSubgroup_mul {X : Type*} (g h : Equiv.Perm X)
    (H : Subgroup (Equiv.Perm X)) :
    relabelSubgroup g (relabelSubgroup h H) = relabelSubgroup (g*h) H :=
  relabelSubgroup_trans h g H

@[simp] theorem relabelSubgroup_one {X : Type*} (H : Subgroup (Equiv.Perm X)) :
    relabelSubgroup (1 : Equiv.Perm X) H = H := relabelSubgroup_refl H

/-- The local family is natural under all original-action internal
normalizers and permutations of equal-action occurrences. Invariance does
not assert that an individual subgroup or lift is fixed. -/
def OrbitProfileFamilyNatural {ι : Type*} (Ω : ι → Type*) (m : ι → ℕ)
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i)))
    (P : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → Prop) : Prop :=
  ∀ w ∈ orbitProfileSymmetries Ω m U, ∀ K, P K → P (relabelSubgroup w K)

/-- A labelling and a permitted actual model subgroup produce their literal
conjugate subgroup on the labelled model set. -/
def orbitProfileLabelMap {ι : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    (P : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → Prop)
    (p : Equiv.Perm (OrbitProfilePoints Ω m) × {K // P K}) :
    Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) := relabelSubgroup p.1 p.2.val

/-- The assembled family consists of actual subgroups admitting a permitted
full orbit presentation. It is not defined by a desired cardinality. -/
def AssembledOrbitProfile {ι : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    (P : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → Prop) :=
  Set.range (orbitProfileLabelMap P)

/-- The associated quotient is equivalent to its literal physical subgroup
image. `orbitProfileLabelMap_eq_iff` identifies its relation as the joint
normalizer action on labels and local subgroups. -/
def orbitProfileAssociatedQuotientEquiv {ι : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    (P : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → Prop) :
    Quotient (Setoid.ker (orbitProfileLabelMap P)) ≃ AssembledOrbitProfile P :=
  Setoid.quotientKerEquivRange _

private theorem orbitProfileLabelMap_full {ι : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {P : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → Prop}
    (hfull : ∀ K, P K → OrbitProfileFull U 1 K)
    (p : Equiv.Perm (OrbitProfilePoints Ω m) × {K // P K}) :
    OrbitProfileFull U p.1 (orbitProfileLabelMap P p) := by
  simpa only [mul_one] using (hfull p.2.val p.2.property).relabel p.1

/-- Equal physical subgroups have exactly the joint internal-symmetry
ambiguity: a change of labels must conjugate the local subgroup back. -/
theorem orbitProfileLabelMap_eq_iff {ι : Type*} {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {P : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → Prop}
    (hfull : ∀ K, P K → OrbitProfileFull U 1 K)
    (htrans : ∀ i (x y : Ω i), ∃ u : U i, (u : Equiv.Perm (Ω i)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (p q : Equiv.Perm (OrbitProfilePoints Ω m) × {K // P K}) :
    orbitProfileLabelMap P q = orbitProfileLabelMap P p ↔
      ∃ w : orbitProfileSymmetries Ω m U,
        q.1 = p.1 * (w : Equiv.Perm (OrbitProfilePoints Ω m)) ∧
          q.2.val = relabelSubgroup (w : Equiv.Perm (OrbitProfilePoints Ω m))⁻¹ p.2.val := by
  constructor
  · intro he
    have hp := orbitProfileLabelMap_full hfull p
    have hq := orbitProfileLabelMap_full hfull q
    rw [he] at hq
    have hw : p.1⁻¹*q.1 ∈ orbitProfileSymmetries Ω m U :=
      (orbitProfileAtlas_eq_iff _ _).mp (hp.atlas_unique hq htrans hsep)
    refine ⟨⟨p.1⁻¹*q.1,hw⟩,by simp,?_⟩
    apply (relabelSubgroup q.1).injective
    change orbitProfileLabelMap P q = _
    rw [relabelSubgroup_mul]
    simpa using he
  · rintro ⟨w,hg,hK⟩
    change relabelSubgroup q.1 q.2.val = relabelSubgroup p.1 p.2.val
    rw [hg,hK,relabelSubgroup_mul]
    simp

/-- Each physical subgroup has one label-pair fibre for every original
internal symmetry, including its possibly nontrivial action on the lift. -/
def orbitProfileLabelFibreEquiv {ι : Type*} {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {P : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → Prop}
    (hfull : ∀ K, P K → OrbitProfileFull U 1 K)
    (hnatural : OrbitProfileFamilyNatural Ω m U P)
    (htrans : ∀ i (x y : Ω i), ∃ u : U i, (u : Equiv.Perm (Ω i)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (p : Equiv.Perm (OrbitProfilePoints Ω m) × {K // P K}) :
    {q // orbitProfileLabelMap P q = orbitProfileLabelMap P p} ≃
      orbitProfileSymmetries Ω m U := by
  classical
  let f : {q // orbitProfileLabelMap P q = orbitProfileLabelMap P p} →
      orbitProfileSymmetries Ω m U := fun q ↦ ⟨p.1⁻¹*q.val.1,by
        obtain ⟨w,hw,_⟩ := (orbitProfileLabelMap_eq_iff hfull htrans hsep p q.val).mp q.property
        simp [hw,w.property]⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro q q' he
    have hg : q.val.1 = q'.val.1 := by
      have hv := congrArg Subtype.val he
      exact mul_left_cancel hv
    apply Subtype.ext
    apply Prod.ext hg
    apply Subtype.ext
    apply (relabelSubgroup q.val.1).injective
    have hc := q.property.trans q'.property.symm
    change relabelSubgroup q.val.1 q.val.2.val = relabelSubgroup q'.val.1 q'.val.2.val at hc
    simpa only [hg] using hc
  · intro w
    let K : {K // P K} := ⟨relabelSubgroup (w : Equiv.Perm (OrbitProfilePoints Ω m))⁻¹ p.2.val,
      hnatural _ ((orbitProfileSymmetries Ω m U).inv_mem w.property) _ p.2.property⟩
    let q := (p.1*(w : Equiv.Perm (OrbitProfilePoints Ω m)),K)
    have hq : orbitProfileLabelMap P q = orbitProfileLabelMap P p :=
      (orbitProfileLabelMap_eq_iff hfull htrans hsep p q).mpr ⟨w,rfl,rfl⟩
    refine ⟨⟨q,hq⟩,?_⟩
    apply Subtype.ext
    change p.1⁻¹*(p.1*(w : Equiv.Perm (OrbitProfilePoints Ω m))) = w
    group

private theorem card_eq_card_mul_of_fibre_card {A B : Type*} [Finite A] [Finite B]
    (f : A → B) (c : ℕ) (hf : ∀ b, Nat.card {a // f a = b} = c) :
    Nat.card A = Nat.card B * c := by
  classical
  letI : Fintype B := Fintype.ofFinite B
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f),Nat.card_sigma]
  simp_rw [hf]
  simp [Nat.card_eq_fintype_card]

/-- Exact assembly over actual subgroups. Atlas and lift data are coupled
by the original symmetry action; the product is a proved cardinal identity. -/
theorem assembledOrbitProfile_card {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {P : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → Prop}
    (hfull : ∀ K, P K → OrbitProfileFull U 1 K)
    (hnatural : OrbitProfileFamilyNatural Ω m U P)
    (htrans : ∀ i (x y : Ω i), ∃ u : U i, (u : Equiv.Perm (Ω i)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U) :
    Nat.card (AssembledOrbitProfile P) =
      Nat.card (LabelledOrbitAtlas Ω m U) * Nat.card {K // P K} := by
  classical
  let f : Equiv.Perm (OrbitProfilePoints Ω m) × {K // P K} → AssembledOrbitProfile P :=
    fun p ↦ ⟨orbitProfileLabelMap P p,⟨p,rfl⟩⟩
  have hf (H : AssembledOrbitProfile P) :
      Nat.card {p // f p = H} = Nat.card (orbitProfileSymmetries Ω m U) := by
    obtain ⟨p,hp⟩ := H.property
    let e : {q // f q = H} ≃ {q // orbitProfileLabelMap P q = orbitProfileLabelMap P p} :=
      Equiv.subtypeEquivRight fun q ↦ by
        change (⟨orbitProfileLabelMap P q,⟨q,rfl⟩⟩ : AssembledOrbitProfile P) = H ↔ _
        rw [Subtype.ext_iff]
        exact Iff.intro (fun h ↦ h.trans hp.symm) (fun h ↦ h.trans hp)
    exact Nat.card_congr (e.trans (orbitProfileLabelFibreEquiv hfull hnatural htrans hsep p))
  have hc := card_eq_card_mul_of_fibre_card f _ hf
  rw [Nat.card_prod] at hc
  have hg : Nat.card (Equiv.Perm (OrbitProfilePoints Ω m)) =
      Nat.card (LabelledOrbitAtlas Ω m U) * Nat.card (orbitProfileSymmetries Ω m U) := by
    rw [← Nat.card_congr (labelledOrbitProfileEquivAtlas Ω m U)]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup (orbitProfileSymmetries Ω m U)
  have hw : 0 < Nat.card (orbitProfileSymmetries Ω m U) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hw
  calc
    Nat.card (AssembledOrbitProfile P) * Nat.card (orbitProfileSymmetries Ω m U) =
        Nat.card (Equiv.Perm (OrbitProfilePoints Ω m)) * Nat.card {K // P K} := hc.symm
    _ = (Nat.card (LabelledOrbitAtlas Ω m U) * Nat.card {K // P K}) *
        Nat.card (orbitProfileSymmetries Ω m U) := by rw [hg]; ring

/-- Original normalizer weights for the actual assembled subgroup family. -/
theorem assembledOrbitProfile_card_rat {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {P : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → Prop}
    (hfull : ∀ K, P K → OrbitProfileFull U 1 K)
    (hnatural : OrbitProfileFamilyNatural Ω m U P)
    (htrans : ∀ i (x y : Ω i), ∃ u : U i, (u : Equiv.Perm (Ω i)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U) :
    (Nat.card (AssembledOrbitProfile P) : ℚ) =
      ((∑ i, m i * Fintype.card (Ω i)).factorial : ℚ) * Nat.card {K // P K} /
        (∏ i, (Nat.card (Subgroup.normalizer (U i : Set (Equiv.Perm (Ω i)))) : ℚ) ^ m i *
          (m i).factorial) := by
  rw [assembledOrbitProfile_card hfull hnatural htrans hsep,Nat.cast_mul,
    labelledOrbitAtlas_card_rat Ω m U]
  ring

/-- Original-action internal coordinate changes preserve literal fullness. -/
theorem OrbitProfileFull.change_frame {ι : Type*} {Ω : ι → Type*}
    [∀ i, Nonempty (Ω i)] {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {g : Equiv.Perm (OrbitProfilePoints Ω m)}
    {H : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m))}
    (hH : OrbitProfileFull U g H) (w : Equiv.Perm (OrbitProfilePoints Ω m))
    (hw : w ∈ orbitProfileSymmetries Ω m U) : OrbitProfileFull U (g*w) H := by
  have hw' := (mem_orbitProfileSymmetries_iff w).mp hw
  constructor
  · intro h i j
    obtain ⟨k,a,ha⟩ := hw' i j
    obtain ⟨v,hv⟩ := hH.maps h i k
    let u : U i := ⟨(a : Equiv.Perm (Ω i))⁻¹ * v * a,
      (Subgroup.mem_normalizer_iff''.mp a.property v).mp v.property⟩
    refine ⟨u,fun x ↦ ?_⟩
    change (h : Equiv.Perm (OrbitProfilePoints Ω m)) (g (w ⟨i,j,x⟩)) =
      g (w ⟨i,j,(u : Equiv.Perm (Ω i)) x⟩)
    rw [ha,ha,hv]
    simp [u]
  · intro i j u
    obtain ⟨k,a,ha⟩ := hw' i j
    let v : U i := ⟨(a : Equiv.Perm (Ω i)) * u * (a : Equiv.Perm (Ω i))⁻¹,
      (Subgroup.mem_normalizer_iff.mp a.property u).mp u.property⟩
    obtain ⟨h,hh⟩ := hH.full i k v
    refine ⟨h,fun x ↦ ?_⟩
    change (h : Equiv.Perm (OrbitProfilePoints Ω m)) (g (w ⟨i,j,x⟩)) =
      g (w ⟨i,j,(u : Equiv.Perm (Ω i)) x⟩)
    rw [ha,ha,hh]
    simp [v]

/-- The entire family of full model subgroups automatically has the required
joint naturality. Special lift families need only prove their extra closure. -/
theorem orbitProfileFull_family_natural {ι : Type*} {Ω : ι → Type*}
    [∀ i, Nonempty (Ω i)] (m : ι → ℕ)
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) :
    OrbitProfileFamilyNatural Ω m U (OrbitProfileFull U 1) := by
  intro w hw K hK
  have hh := (hK.relabel w).change_frame w⁻¹ ((orbitProfileSymmetries Ω m U).inv_mem hw)
  simpa only [mul_one,mul_inv_cancel] using hh

/-- Actual full profile subgroups on any common labelled point set. -/
def AssembledOrbitProfileOn {ι : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    (P : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → Prop) (X : Type*) :=
  {H : Subgroup (Equiv.Perm X) // ∃ e : OrbitProfilePoints Ω m ≃ X,
    ∃ K, P K ∧ relabelSubgroup e K = H}

/-- Relabelling gives an equivalence of the actual subgroup families; no
choice of internal frame is remembered by an element of either family. -/
def assembledOrbitProfileEquivOn {ι X : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    (P : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → Prop)
    (e : OrbitProfilePoints Ω m ≃ X) :
    AssembledOrbitProfile P ≃ AssembledOrbitProfileOn P X := by
  let f : AssembledOrbitProfile P → AssembledOrbitProfileOn P X := fun H ↦
    ⟨relabelSubgroup e H.val,by
      obtain ⟨p,hp⟩ := H.property
      refine ⟨p.1.trans e,p.2.val,p.2.property,?_⟩
      rw [← relabelSubgroup_trans]
      exact congrArg (relabelSubgroup e) hp⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro H K he
    apply Subtype.ext
    exact (relabelSubgroup e).injective (congrArg Subtype.val he)
  · rintro ⟨H,g,K,hK,hH⟩
    let p : Equiv.Perm (OrbitProfilePoints Ω m) × {K // P K} :=
      (g.trans e.symm,⟨K,hK⟩)
    refine ⟨⟨orbitProfileLabelMap P p,⟨p,rfl⟩⟩,?_⟩
    apply Subtype.ext
    change relabelSubgroup e (relabelSubgroup (g.trans e.symm) K) = H
    rw [relabelSubgroup_trans]
    have he : (g.trans e.symm).trans e = g := by ext x; simp
    rw [he,hH]

theorem AssembledOrbitProfileOn.full {ι X : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {P : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → Prop}
    (hfull : ∀ K, P K → OrbitProfileFull U 1 K) (H : AssembledOrbitProfileOn P X) :
    ∃ e : OrbitProfilePoints Ω m ≃ X, OrbitProfileFullOn U e H.val := by
  obtain ⟨e,K,hK,hH⟩ := H.property
  refine ⟨e,?_⟩
  rw [← hH]
  exact ((orbitProfileFullOn_iff _ _ _).mpr (hfull K hK)).relabel e

/-- Different multiplicity profiles are disjoint as families of actual
subgroups on the same labels, including equal-degree different actions. -/
theorem assembledOrbitProfileOn_disjoint {ι X : Type*} {Ω : ι → Type*}
    [∀ i, Nonempty (Ω i)] {m m' : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {P : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → Prop}
    {P' : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m')) → Prop}
    (hfull : ∀ K, P K → OrbitProfileFull U 1 K)
    (hfull' : ∀ K, P' K → OrbitProfileFull U 1 K)
    (htrans : ∀ i (x y : Ω i), ∃ u : U i, (u : Equiv.Perm (Ω i)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (H : AssembledOrbitProfileOn P X) (H' : AssembledOrbitProfileOn P' X)
    (he : H.val = H'.val) : m = m' := by
  obtain ⟨g,hg⟩ := H.full hfull
  obtain ⟨h,hh⟩ := H'.full hfull'
  rw [← he] at hh
  exact hg.multiplicity_unique hh htrans hsep

/-- The exact physical profile weight on an arbitrary labelled set. -/
theorem assembledOrbitProfileOn_card_rat {ι X : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {P : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → Prop}
    (e : OrbitProfilePoints Ω m ≃ X)
    (hfull : ∀ K, P K → OrbitProfileFull U 1 K)
    (hnatural : OrbitProfileFamilyNatural Ω m U P)
    (htrans : ∀ i (x y : Ω i), ∃ u : U i, (u : Equiv.Perm (Ω i)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U) :
    (Nat.card (AssembledOrbitProfileOn P X) : ℚ) =
      ((∑ i, m i * Fintype.card (Ω i)).factorial : ℚ) * Nat.card {K // P K} /
        (∏ i, (Nat.card (Subgroup.normalizer (U i : Set (Equiv.Perm (Ω i)))) : ℚ) ^ m i *
          (m i).factorial) := by
  rw [← Nat.card_congr (assembledOrbitProfileEquivOn P e)]
  exact assembledOrbitProfile_card_rat hfull hnatural htrans hsep

/-- The physical full-profile condition itself, without any remembered
presentation or supplementary local-family predicate. -/
def FullOrbitProfileOn {ι : Type*} (Ω : ι → Type*) (m : ι → ℕ)
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) (X : Type*) :=
  {H : Subgroup (Equiv.Perm X) //
    ∃ e : OrbitProfilePoints Ω m ≃ X, OrbitProfileFullOn U e H}

def assembledFullOrbitProfileEquiv {ι X : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) :
    AssembledOrbitProfileOn (OrbitProfileFull (m := m) U 1) X ≃ FullOrbitProfileOn Ω m U X :=
  Equiv.subtypeEquivRight fun H ↦ by
    constructor
    · intro hH
      exact AssembledOrbitProfileOn.full (fun _ h ↦ h) ⟨H,hH⟩
    · rintro ⟨e,he⟩
      refine ⟨e,relabelSubgroup e.symm H,?_,?_⟩
      · apply (orbitProfileFullOn_iff _ _ _).mp
        have hh := he.relabel e.symm
        simpa only [Equiv.self_trans_symm] using hh
      · exact relabelSubgroup_symm e.symm H

/-- An unconditional profile-weight theorem for all full subgroups of the
given transitive, distinct original actions. No naturality premise remains. -/
theorem fullOrbitProfileOn_card_rat {ι X : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] (m : ι → ℕ)
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) (e : OrbitProfilePoints Ω m ≃ X)
    (htrans : ∀ i (x y : Ω i), ∃ u : U i, (u : Equiv.Perm (Ω i)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U) :
    (Nat.card (FullOrbitProfileOn Ω m U X) : ℚ) =
      ((∑ i, m i * Fintype.card (Ω i)).factorial : ℚ) *
        Nat.card {K // OrbitProfileFull (m := m) U 1 K} /
        (∏ i, (Nat.card (Subgroup.normalizer (U i : Set (Equiv.Perm (Ω i)))) : ℚ) ^ m i *
          (m i).factorial) := by
  rw [← Nat.card_congr (assembledFullOrbitProfileEquiv U)]
  exact assembledOrbitProfileOn_card_rat e (fun _ h ↦ h)
    (orbitProfileFull_family_natural m U) htrans hsep

/-- A union of multiplicity profiles, still a subtype of actual subgroups
on the single labelled set `X`. -/
def AssembledOrbitProfilesOn {τ ι : Type*} {Ω : ι → Type*} (m : τ → ι → ℕ)
    (P : ∀ t, Subgroup (Equiv.Perm (OrbitProfilePoints Ω (m t))) → Prop) (X : Type*) :=
  {H : Subgroup (Equiv.Perm X) // ∃ t, ∃ e : OrbitProfilePoints Ω (m t) ≃ X,
    ∃ K, P t K ∧ relabelSubgroup e K = H}

/-- Forgetting the profile index is bijective, because the actual subgroup
recovers the multiplicity vector. -/
def assembledOrbitProfilesSigmaEquiv {τ ι X : Type*} {Ω : ι → Type*}
    [∀ i, Nonempty (Ω i)] {m : τ → ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {P : ∀ t, Subgroup (Equiv.Perm (OrbitProfilePoints Ω (m t))) → Prop}
    (hm : Function.Injective m)
    (hfull : ∀ t K, P t K → OrbitProfileFull U 1 K)
    (htrans : ∀ i (x y : Ω i), ∃ u : U i, (u : Equiv.Perm (Ω i)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U) :
    (Σ t, AssembledOrbitProfileOn (P t) X) ≃ AssembledOrbitProfilesOn m P X := by
  let f : (Σ t, AssembledOrbitProfileOn (P t) X) → AssembledOrbitProfilesOn m P X :=
    fun q ↦ ⟨q.2.val,q.1,q.2.property⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · rintro ⟨t,H⟩ ⟨s,K⟩ he
    have hHK : H.val = K.val := congrArg Subtype.val he
    have hts : t = s := hm (assembledOrbitProfileOn_disjoint (hfull t) (hfull s)
      htrans hsep H K hHK)
    subst s
    have he' : H=K := Subtype.ext hHK
    subst K
    rfl
  · rintro ⟨H,t,hH⟩
    exact ⟨⟨t,⟨H,hH⟩⟩,rfl⟩

/-- Exact sum of original-action weights over pairwise distinct full
profiles. Fullness, naturality, and action separation are verified locally;
the summation contains no duplicated physical subgroup. -/
theorem assembledOrbitProfilesOn_card_rat {τ ι X : Type*} [Fintype τ] [Fintype ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    {m : τ → ι → ℕ} {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {P : ∀ t, Subgroup (Equiv.Perm (OrbitProfilePoints Ω (m t))) → Prop}
    (e : ∀ t, OrbitProfilePoints Ω (m t) ≃ X) (hm : Function.Injective m)
    (hfull : ∀ t K, P t K → OrbitProfileFull U 1 K)
    (hnatural : ∀ t, OrbitProfileFamilyNatural Ω (m t) U (P t))
    (htrans : ∀ i (x y : Ω i), ∃ u : U i, (u : Equiv.Perm (Ω i)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U) :
    (Nat.card (AssembledOrbitProfilesOn m P X) : ℚ) =
      ∑ t, ((∑ i, m t i * Fintype.card (Ω i)).factorial : ℚ) * Nat.card {K // P t K} /
        (∏ i, (Nat.card (Subgroup.normalizer (U i : Set (Equiv.Perm (Ω i)))) : ℚ) ^ m t i *
          (m t i).factorial) := by
  classical
  letI : ∀ t, Finite (AssembledOrbitProfileOn (P t) X) := fun t ↦
    Finite.of_equiv (AssembledOrbitProfile (P t)) (assembledOrbitProfileEquivOn (P t) (e t))
  rw [← Nat.card_congr (assembledOrbitProfilesSigmaEquiv hm hfull htrans hsep),
    Nat.card_sigma,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro t ht
  exact assembledOrbitProfileOn_card_rat (e t) (hfull t) (hnatural t) htrans hsep

/-- A concrete identification with the usual `n` labelled points, derived
from the sum of original action degrees. -/
def orbitProfileFinLabels {ι : Type*} [Fintype ι] (Ω : ι → Type*)
    [∀ i, Fintype (Ω i)] (m : ι → ℕ) (n : ℕ)
    (hn : ∑ i, m i * Fintype.card (Ω i) = n) : OrbitProfilePoints Ω m ≃ Fin n :=
  Fintype.equivFinOfCardEq (by
    simpa [OrbitProfilePoints,Fintype.card_sigma,Fintype.card_prod] using hn)

/-- The exact all-full-subgroup profile formula in the symmetric group on
`Fin n`, with the original permutation normalizers in the denominator. -/
theorem fullOrbitProfileOn_fin_card_rat {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] (m : ι → ℕ)
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) (n : ℕ)
    (hn : ∑ i, m i * Fintype.card (Ω i) = n)
    (htrans : ∀ i (x y : Ω i), ∃ u : U i, (u : Equiv.Perm (Ω i)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U) :
    (Nat.card (FullOrbitProfileOn Ω m U (Fin n)) : ℚ) =
      (n.factorial : ℚ) * Nat.card {K // OrbitProfileFull (m := m) U 1 K} /
        (∏ i, (Nat.card (Subgroup.normalizer (U i : Set (Equiv.Perm (Ω i)))) : ℚ) ^ m i *
          (m i).factorial) := by
  simpa only [hn] using fullOrbitProfileOn_card_rat m U (orbitProfileFinLabels Ω m n hn) htrans hsep

/-- Summing permitted natural lift families in the actual `S_n` multiplies
each model fibre by its original profile weight exactly once. -/
theorem assembledOrbitProfilesOn_fin_card_rat {τ ι : Type*} [Fintype τ] [Fintype ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    {m : τ → ι → ℕ} {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {P : ∀ t, Subgroup (Equiv.Perm (OrbitProfilePoints Ω (m t))) → Prop}
    (n : ℕ) (hn : ∀ t, ∑ i, m t i * Fintype.card (Ω i) = n)
    (hm : Function.Injective m)
    (hfull : ∀ t K, P t K → OrbitProfileFull U 1 K)
    (hnatural : ∀ t, OrbitProfileFamilyNatural Ω (m t) U (P t))
    (htrans : ∀ i (x y : Ω i), ∃ u : U i, (u : Equiv.Perm (Ω i)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U) :
    (Nat.card (AssembledOrbitProfilesOn m P (Fin n)) : ℚ) =
      ∑ t, (n.factorial : ℚ) * Nat.card {K // P t K} /
        (∏ i, (Nat.card (Subgroup.normalizer (U i : Set (Equiv.Perm (Ω i)))) : ℚ) ^ m t i *
          (m t i).factorial) := by
  simpa only [hn] using assembledOrbitProfilesOn_card_rat
    (fun t ↦ orbitProfileFinLabels Ω (m t) n (hn t)) hm hfull hnatural htrans hsep

end SymmetricSubgroupAsymptotics
