import SymmetricSubgroupAsymptotics.EpimorphismKernelLabels
import SymmetricSubgroupAsymptotics.CompleteQuotientMoment
import SymmetricSubgroupAsymptotics.SemisimpleNormalChart
import Mathlib.GroupTheory.Subgroup.Simple

/-!
# The semisimple outer fibre

Let `E ◁ U` be a direct product of nonabelian simple groups and `R = U/E`.
For every finite source `J`,

`Z_J(U) ≤ Z_J(R) · ∏ᵢ (1 + |Aut Sᵢ| · log|J| / log|Sᵢ|)`.

The proof groups the literal normal subgroups `N` of `U` by `N ∩ E`, which is
a subproduct of the simple factors, and by `NE/E ◁ R`; these two data
determine `N`.  An onto map `J → U/N` is determined by its outer map onto
`U/NE` and its restriction onto the centerless image of `E`.  Finally the
number of normal subgroups of a finite `F` with a fixed nonabelian simple
quotient `S` is at most `log|F| / log|S|`, because such kernels are jointly
surjective.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-! ## Normal subgroups of a product of centerless simple groups -/

section Subproduct

variable {ι : Type*} [DecidableEq ι] {S : ι → Type*} [∀ i, Group (S i)]

/-- A normal subgroup with a nontrivial coordinate contains that whole
factor. -/
theorem pi_mulSingle_mem_of_coordinate (hsimple : ∀ i, IsSimpleGroup (S i))
    (hZ : ∀ i, IsCenterless (S i)) (N : Subgroup (∀ i, S i)) (hN : N.Normal)
    {i : ι} (hi : ∃ y ∈ N, y i ≠ 1) (s : S i) : Pi.mulSingle i s ∈ N := by
  obtain ⟨y, hyN, hyi⟩ := hi
  obtain ⟨t, ht⟩ : ∃ t : S i, y i * t ≠ t * y i := by
    by_contra hall
    push Not at hall
    exact hyi (hZ i (y i) hall)
  let A : Subgroup (S i) := N.comap (MonoidHom.mulSingle S i)
  have hA : A.Normal := ⟨fun a ha g => by
    change Pi.mulSingle i (g * a * g⁻¹) ∈ N
    have : Pi.mulSingle i (g * a * g⁻¹) =
        Pi.mulSingle i g * Pi.mulSingle i a * (Pi.mulSingle i g)⁻¹ := by
      rw [Pi.mulSingle_mul, Pi.mulSingle_mul, Pi.mulSingle_inv]
    rw [this]
    exact hN.conj_mem _ ha _⟩
  let c : S i := y i * t * (y i)⁻¹ * t⁻¹
  have hc : c ∈ A := by
    change Pi.mulSingle i c ∈ N
    have heq : Pi.mulSingle i c =
        y * (Pi.mulSingle i t * y⁻¹ * (Pi.mulSingle i t)⁻¹) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [c, mul_assoc]
      · simp [Pi.mulSingle_eq_of_ne hj]
    rw [heq]
    exact N.mul_mem hyN (hN.conj_mem _ (N.inv_mem hyN) _)
  have hc1 : c ≠ 1 := by
    intro h1
    apply ht
    have : y i * t * (y i)⁻¹ * t⁻¹ = 1 := h1
    calc y i * t = (y i * t * (y i)⁻¹ * t⁻¹) * (t * y i) := by group
      _ = t * y i := by rw [this, one_mul]
  rcases (hsimple i).eq_bot_or_eq_top_of_normal A hA with hbot | htop
  · exact absurd (hbot ▸ hc : c ∈ (⊥ : Subgroup (S i))) (by
      rw [Subgroup.mem_bot]
      exact hc1)
  · have : s ∈ A := htop ▸ Subgroup.mem_top s
    exact this

variable [Fintype ι]

/-- Normal subgroups of a finite product of centerless simple groups are
subproducts: membership is decided by the coordinates in the support. -/
theorem pi_normal_mem_iff (hsimple : ∀ i, IsSimpleGroup (S i))
    (hZ : ∀ i, IsCenterless (S i)) (N : Subgroup (∀ i, S i)) (hN : N.Normal)
    (x : ∀ i, S i) :
    x ∈ N ↔ ∀ i, (∀ y ∈ N, y i = 1) → x i = 1 := by
  constructor
  · intro hx i hi
    exact hi x hx
  · intro hx
    have key : ∀ s : Finset ι, ∀ x : ∀ i, S i, (∀ i ∉ s, x i = 1) →
        (∀ i, (∀ y ∈ N, y i = 1) → x i = 1) → x ∈ N := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro x hout _
        have : x = 1 := funext fun i => hout i (Finset.notMem_empty i)
        rw [this]
        exact N.one_mem
      | insert j t hjt ih =>
        intro x hout hsupp
        let x' : ∀ i, S i := x * (Pi.mulSingle j (x j))⁻¹
        have hx' : x = x' * Pi.mulSingle j (x j) := by simp [x']
        rw [hx']
        refine N.mul_mem (ih x' ?_ ?_) ?_
        · intro i hi
          by_cases hij : i = j
          · subst hij
            simp [x']
          · have := hout i (by simp [hij, hi])
            simp [x', Pi.mulSingle_eq_of_ne hij, this]
        · intro i hi
          by_cases hij : i = j
          · subst hij
            simp [x']
          · simp [x', Pi.mulSingle_eq_of_ne hij, hsupp i hi]
        · by_cases hxj : x j = 1
          · rw [hxj, Pi.mulSingle_one]
            exact N.one_mem
          · apply pi_mulSingle_mem_of_coordinate hsimple hZ N hN
            by_contra hall
            push Not at hall
            exact hxj (hsupp j hall)
    exact key Finset.univ x (fun i hi => absurd (Finset.mem_univ i) hi) hx

/-- Modulo a normal subgroup, an element commuting with everything lies in
the subgroup. -/
theorem pi_mem_of_commutators_mem (hsimple : ∀ i, IsSimpleGroup (S i))
    (hZ : ∀ i, IsCenterless (S i)) (N : Subgroup (∀ i, S i)) (hN : N.Normal)
    (x : ∀ i, S i) (hx : ∀ y : ∀ i, S i, x * y * x⁻¹ * y⁻¹ ∈ N) : x ∈ N := by
  rw [pi_normal_mem_iff hsimple hZ N hN]
  intro i hi
  apply hZ i
  intro t
  have h := hi _ (hx (Pi.mulSingle i t))
  simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same] at h
  calc x i * t = (x i * t * (x i)⁻¹ * t⁻¹) * (t * x i) := by group
    _ = t * x i := by rw [h, one_mul]

end Subproduct

/-! ## Distinct simple-quotient kernels are independent -/

/-- A proper normal subgroup of a finite product of centerless simple groups
is trivial on some coordinate. -/
theorem pi_normal_exists_trivial_coordinate {ι : Type*} [DecidableEq ι] [Fintype ι]
    (S : ι → Type*) [∀ i, Group (S i)] (hsimple : ∀ i, IsSimpleGroup (S i))
    (hZ : ∀ i, IsCenterless (S i)) (N : Subgroup (∀ i, S i)) (hN : N.Normal)
    (hne : N ≠ ⊤) : ∃ i, ∀ y ∈ N, y i = 1 := by
  by_contra hall
  push Not at hall
  apply hne
  rw [eq_top_iff]
  intro y _
  rw [pi_normal_mem_iff hsimple hZ N hN]
  intro i hi
  obtain ⟨z, hz, hzi⟩ := hall i
  exact absurd (hi z hz) hzi

section SimpleQuotients

variable {F : Type*} [Group F]

theorem simpleQuotient_ne_top (K : {N : Subgroup F // N.Normal})
    (h : IsSimpleGroup (F ⧸ K.1)) : K.1 ≠ ⊤ := by
  intro htop
  obtain ⟨a, b, hab⟩ := h.toNontrivial.exists_pair_ne
  apply hab
  induction a using QuotientGroup.induction_on
  induction b using QuotientGroup.induction_on
  rw [QuotientGroup.eq, htop]
  trivial

/-- A kernel with simple quotient is maximal among proper normal
subgroups. -/
theorem simpleQuotient_eq_of_le (K₀ K₁ : {N : Subgroup F // N.Normal})
    (h₀ : IsSimpleGroup (F ⧸ K₀.1)) (h₁ : IsSimpleGroup (F ⧸ K₁.1))
    (hle : K₀.1 ≤ K₁.1) : K₀ = K₁ := by
  apply Subtype.ext
  let B : Subgroup (F ⧸ K₀.1) := K₁.1.map (QuotientGroup.mk' K₀.1)
  have hB : B.Normal := Subgroup.Normal.map K₁.2 _ (QuotientGroup.mk'_surjective _)
  rcases h₀.eq_bot_or_eq_top_of_normal B hB with hbot | htop
  · apply le_antisymm hle
    intro f hf
    have : (QuotientGroup.mk' K₀.1 f) ∈ B := ⟨f, hf, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff f).mp this
  · exfalso
    apply simpleQuotient_ne_top K₁ h₁
    rw [eq_top_iff]
    intro f _
    have : (QuotientGroup.mk' K₀.1 f) ∈ B := htop ▸ Subgroup.mem_top _
    obtain ⟨g, hg, hgf⟩ := this
    have hgf' : g⁻¹ * f ∈ K₀.1 := QuotientGroup.eq.mp hgf
    have := K₁.1.mul_mem hg (hle hgf')
    simpa using this

/-- The inductive step: a new simple-quotient kernel containing the joint
kernel of `t` must already belong to `t`. -/
theorem simpleQuotient_mem_of_joint_le
    (t : Finset {N : Subgroup F // N.Normal})
    (hsimple : ∀ K ∈ t, IsSimpleGroup (F ⧸ K.1))
    (hZ : ∀ K ∈ t, IsCenterless (F ⧸ K.1))
    (hsurj : ∀ v : (K : {N : Subgroup F // N.Normal}) → F ⧸ K.1,
      ∃ f : F, ∀ K ∈ t, (f : F ⧸ K.1) = v K)
    (K₀ : {N : Subgroup F // N.Normal}) (h₀ : IsSimpleGroup (F ⧸ K₀.1))
    (hM : ∀ f : F, (∀ K ∈ t, f ∈ K.1) → f ∈ K₀.1) : K₀ ∈ t := by
  let S' : t → Type _ := fun K => F ⧸ K.1.1
  let ψ : F →* ((K : t) → S' K) :=
    Pi.monoidHom (fun K : t => QuotientGroup.mk' K.1.1)
  have hψ : Function.Surjective ψ := by
    intro v
    obtain ⟨f, hf⟩ := hsurj (fun K => if h : K ∈ t then v ⟨K, h⟩ else 1)
    refine ⟨f, funext fun K => ?_⟩
    have := hf K.1 K.2
    simp only [K.2, dif_pos] at this
    exact this
  let K₀' : Subgroup ((K : t) → S' K) := K₀.1.map ψ
  have hK₀' : K₀'.Normal := Subgroup.Normal.map K₀.2 ψ hψ
  have hcomap : K₀'.comap ψ = K₀.1 := by
    rw [Subgroup.comap_map_eq]
    apply sup_eq_left.mpr
    intro f hf
    apply hM
    intro K hK
    have := congrFun hf ⟨K, hK⟩
    exact (QuotientGroup.eq_one_iff f).mp this
  have hne : K₀' ≠ ⊤ := by
    intro htop
    apply simpleQuotient_ne_top K₀ h₀
    rw [← hcomap, htop, Subgroup.comap_top]
  obtain ⟨K₁, hK₁⟩ := pi_normal_exists_trivial_coordinate S'
    (fun K => hsimple K.1 K.2) (fun K => hZ K.1 K.2) K₀' hK₀' hne
  have hle : K₀.1 ≤ K₁.1.1 := by
    intro f hf
    have hmem : ψ f ∈ K₀' := ⟨f, hf, rfl⟩
    exact (QuotientGroup.eq_one_iff f).mp (hK₁ _ hmem)
  have heq := simpleQuotient_eq_of_le K₀ K₁.1 h₀ (hsimple K₁.1 K₁.2) hle
  exact heq ▸ K₁.2

/-- Normal subgroups with pairwise distinct centerless simple quotients are
jointly surjective. -/
theorem simpleQuotients_jointly_surjective
    (s : Finset {N : Subgroup F // N.Normal})
    (hsimple : ∀ K ∈ s, IsSimpleGroup (F ⧸ K.1))
    (hZ : ∀ K ∈ s, IsCenterless (F ⧸ K.1)) :
    ∀ v : (K : {N : Subgroup F // N.Normal}) → F ⧸ K.1,
      ∃ f : F, ∀ K ∈ s, (f : F ⧸ K.1) = v K := by
  induction s using Finset.induction_on with
  | empty => exact fun _ => ⟨1, fun K hK => absurd hK (Finset.notMem_empty K)⟩
  | insert K₀ t hK₀ ih =>
    have hsimple_t : ∀ K ∈ t, IsSimpleGroup (F ⧸ K.1) :=
      fun K hK => hsimple K (Finset.mem_insert_of_mem hK)
    have hZ_t : ∀ K ∈ t, IsCenterless (F ⧸ K.1) :=
      fun K hK => hZ K (Finset.mem_insert_of_mem hK)
    have ih' := ih hsimple_t hZ_t
    have h₀ : IsSimpleGroup (F ⧸ K₀.1) := hsimple K₀ (Finset.mem_insert_self _ _)
    let M : Subgroup F := ⨅ K ∈ t, K.1
    have hM : ∀ f, f ∈ M ↔ ∀ K ∈ t, f ∈ K.1 := by
      intro f
      simp only [M, Subgroup.mem_iInf]
    have hMnormal : M.Normal := ⟨fun f hf g => by
      rw [hM] at hf ⊢
      intro K hK
      exact K.2.conj_mem f (hf K hK) g⟩
    let A : Subgroup (F ⧸ K₀.1) := M.map (QuotientGroup.mk' K₀.1)
    have hA : A.Normal :=
      Subgroup.Normal.map hMnormal _ (QuotientGroup.mk'_surjective _)
    have hAtop : A = ⊤ := by
      rcases h₀.eq_bot_or_eq_top_of_normal A hA with hbot | htop
      · exfalso
        apply hK₀
        apply simpleQuotient_mem_of_joint_le t hsimple_t hZ_t ih' K₀ h₀
        intro f hf
        have : (QuotientGroup.mk' K₀.1 f) ∈ A := ⟨f, (hM f).mpr hf, rfl⟩
        rw [hbot, Subgroup.mem_bot] at this
        exact (QuotientGroup.eq_one_iff f).mp this
      · exact htop
    intro v
    obtain ⟨f₁, hf₁⟩ := ih' v
    have hmem : ((f₁ : F ⧸ K₀.1))⁻¹ * v K₀ ∈ A := hAtop ▸ Subgroup.mem_top _
    obtain ⟨f₂, hf₂M, hf₂⟩ := hmem
    refine ⟨f₁ * f₂, fun K hK => ?_⟩
    rcases Finset.mem_insert.mp hK with hKK | hKt
    · subst hKK
      rw [QuotientGroup.mk_mul]
      change (f₁ : F ⧸ K.1) * QuotientGroup.mk' K.1 f₂ = v K
      rw [hf₂, mul_inv_cancel_left]
    · rw [QuotientGroup.mk_mul, hf₁ K hKt]
      have : (f₂ : F ⧸ K.1) = 1 :=
        (QuotientGroup.eq_one_iff f₂).mpr ((hM f₂).mp hf₂M K hKt)
      rw [this, mul_one]

/-- Onto maps to a centerless simple group:
`|Epi(F,S)| ≤ |Aut S| · log|F| / log|S|`. -/
theorem simpleGroupEpimorphism_card_le [Finite F] {S : Type*} [Group S]
    [Finite S] (hsimple : IsSimpleGroup S) (hZ : IsCenterless S) :
    (Nat.card (GroupEpimorphism F S) : ℝ) ≤
      Nat.card (S ≃* S) *
        (Real.logb 2 (Nat.card F) / Real.logb 2 (Nat.card S)) := by
  -- kernels of onto maps
  let κ : GroupEpimorphism F S → {N : Subgroup F // N.Normal} :=
    fun f => ⟨f.1.ker, MonoidHom.normal_ker f.1⟩
  let L := Set.range κ
  letI : Fintype L := Fintype.ofFinite L
  have hlabel := groupEpimorphism_card_le_kernel_labels
    (fun f => (⟨κ f, f, rfl⟩ : L))
    (fun f g h => congrArg (fun K : L => K.1.1) h)
  -- each kernel has quotient `S`
  have hquot : ∀ K : L, Nonempty ((F ⧸ K.1.1) ≃* S) := by
    intro K
    obtain ⟨f, hf⟩ := K.2
    rw [← hf]
    exact ⟨QuotientGroup.quotientKerEquivOfSurjective f.1 f.2⟩
  let s : Finset {N : Subgroup F // N.Normal} := Finset.univ.filter (· ∈ L)
  have hs : ∀ K ∈ s, K ∈ L := fun K hK => (Finset.mem_filter.mp hK).2
  have hsimple_s : ∀ K ∈ s, IsSimpleGroup (F ⧸ K.1) := by
    intro K hK
    obtain ⟨e⟩ := hquot ⟨K, hs K hK⟩
    haveI := hsimple
    exact e.isSimpleGroup
  have hZ_s : ∀ K ∈ s, IsCenterless (F ⧸ K.1) := by
    intro K hK x hx
    obtain ⟨e⟩ := hquot ⟨K, hs K hK⟩
    have := hZ (e x) (fun y => by
      obtain ⟨z, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, hx z])
    exact e.injective (this.trans e.map_one.symm)
  have hsurj := simpleQuotients_jointly_surjective s hsimple_s hZ_s
  -- `|S|^{#L} ≤ |F|`
  let Φ : F → ((K : s) → F ⧸ K.1.1) := fun f K => (f : F ⧸ K.1.1)
  have hΦ : Function.Surjective Φ := by
    intro v
    obtain ⟨f, hf⟩ := hsurj (fun K => if h : K ∈ s then v ⟨K, h⟩ else 1)
    refine ⟨f, funext fun K => ?_⟩
    have := hf K.1 K.2
    simp only [K.2, dif_pos] at this
    exact this
  have hcardΦ := Nat.card_le_card_of_surjective Φ hΦ
  have hs_card : Nat.card s = Nat.card L := by
    apply Nat.card_congr
    exact { toFun := fun K => ⟨K.1, hs K.1 K.2⟩
            invFun := fun K => ⟨K.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, K.2⟩⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  have hprod : Nat.card ((K : s) → F ⧸ K.1.1) = Nat.card S ^ Nat.card L := by
    calc Nat.card ((K : s) → F ⧸ K.1.1) = ∏ K : s, Nat.card (F ⧸ K.1.1) :=
          Nat.card_pi
      _ = ∏ _K : s, Nat.card S := by
          apply Finset.prod_congr rfl
          intro K _
          obtain ⟨e⟩ := hquot ⟨K.1, hs K.1 K.2⟩
          exact Nat.card_congr e.toEquiv
      _ = Nat.card S ^ Nat.card L := by
          rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
            hs_card]
  rw [hprod] at hcardΦ
  have hS1 : 1 < Nat.card S := by
    haveI := hsimple.toNontrivial
    exact Finite.one_lt_card
  have hlogS : 0 < Real.logb 2 (Nat.card S) :=
    Real.logb_pos (by norm_num) (by exact_mod_cast hS1)
  have hL : (Nat.card L : ℝ) ≤ Real.logb 2 (Nat.card F) / Real.logb 2 (Nat.card S) := by
    rw [le_div_iff₀ hlogS]
    have h1 : ((Nat.card S ^ Nat.card L : ℕ) : ℝ) ≤ Nat.card F := by
      exact_mod_cast hcardΦ
    have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num)
      (by positivity) h1
    rw [Nat.cast_pow, Real.logb_pow] at h2
    linarith
  calc (Nat.card (GroupEpimorphism F S) : ℝ)
      ≤ ((Nat.card L * Nat.card (S ≃* S) : ℕ) : ℝ) := by exact_mod_cast hlabel
    _ = Nat.card (S ≃* S) * (Nat.card L : ℝ) := by push_cast; ring
    _ ≤ Nat.card (S ≃* S) *
        (Real.logb 2 (Nat.card F) / Real.logb 2 (Nat.card S)) :=
        mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg _)

end SimpleQuotients


/-! ## The outer fibre of a semisimple normal subgroup -/

/-- The image of `E` in `U/N`. -/
def quotientImage {U : Type*} [Group U] (E : Subgroup U)
    (N : {N : Subgroup U // N.Normal}) : Subgroup (U ⧸ N.1) :=
  E.map (QuotientGroup.mk' N.1)

/-- The outer quotient map `U/N → U/NE`. -/
def quotientOuter {U : Type*} [Group U] (E : Subgroup U) [E.Normal]
    (N : {N : Subgroup U // N.Normal}) : U ⧸ N.1 →* U ⧸ (N.1 ⊔ E) :=
  QuotientGroup.map N.1 (N.1 ⊔ E) (MonoidHom.id U)
    (fun _ hx => (le_sup_left : N.1 ≤ N.1 ⊔ E) hx)

theorem mem_quotientImage_of_outer {U : Type*} [Group U] (E : Subgroup U) [E.Normal]
    (N : {N : Subgroup U // N.Normal}) (q : U ⧸ N.1)
    (hq : quotientOuter E N q = 1) : q ∈ quotientImage E N := by
  induction q using QuotientGroup.induction_on with | H u => ?_
  have hu : u ∈ N.1 ⊔ E := (QuotientGroup.eq_one_iff u).mp hq
  obtain ⟨n, hn, x, hx, rfl⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := N.1) (t := E)).mp hu
  refine ⟨x, hx, ?_⟩
  change (x : U ⧸ N.1) = ((n * x : U) : U ⧸ N.1)
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]

theorem quotientOuter_image {U : Type*} [Group U] (E : Subgroup U) [E.Normal]
    (N : {N : Subgroup U // N.Normal}) (q : U ⧸ N.1)
    (hq : q ∈ quotientImage E N) : quotientOuter E N q = 1 := by
  obtain ⟨x, hx, rfl⟩ := hq
  exact (QuotientGroup.eq_one_iff x).mpr ((le_sup_right : E ≤ N.1 ⊔ E) hx)

namespace SemisimpleNormalChart

variable {U : Type*} [Group U] {E : Subgroup U} (C : SemisimpleNormalChart E)

/-- The weight `|Aut Sᵢ| · L / log₂|Sᵢ|` of one simple factor. -/
def factorWeight (L : ℝ) (i : C.ι) : ℝ :=
  Nat.card (C.factor i ≃* C.factor i) *
    (L / Real.logb 2 (Nat.card (C.factor i)))

/-- `Ψ_E(L) = ∏ᵢ (1 + |Aut Sᵢ| · L / log₂|Sᵢ|)`. -/
def outerFactor (L : ℝ) : ℝ := ∏ i, (1 + C.factorWeight L i)

theorem logb_card_pos (i : C.ι) : 0 < Real.logb 2 (Nat.card (C.factor i)) := by
  haveI := (C.simple i).toNontrivial
  exact Real.logb_pos (by norm_num) (by exact_mod_cast Finite.one_lt_card)

theorem factorWeight_nonneg {L : ℝ} (hL : 0 ≤ L) (i : C.ι) :
    0 ≤ C.factorWeight L i :=
  mul_nonneg (Nat.cast_nonneg _) (div_nonneg hL (C.logb_card_pos i).le)

theorem factorWeight_mono {L L' : ℝ} (h : L ≤ L') (i : C.ι) :
    C.factorWeight L i ≤ C.factorWeight L' i :=
  mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h (C.logb_card_pos i).le)
    (Nat.cast_nonneg _)

theorem outerFactor_nonneg {L : ℝ} (hL : 0 ≤ L) : 0 ≤ C.outerFactor L :=
  Finset.prod_nonneg (fun i _ => by linarith [C.factorWeight_nonneg hL i])

variable [E.Normal]

/-- The simple factors met by a normal subgroup. -/
def support (N : {N : Subgroup U // N.Normal}) : Finset C.ι :=
  Finset.univ.filter fun i => ∃ x : E, (x : U) ∈ N.1 ∧ C.equiv x i ≠ 1

/-- The image of `N ∩ E` in the product of the simple factors. -/
def meetImage (N : {N : Subgroup U // N.Normal}) :
    Subgroup ((i : C.ι) → C.factor i) :=
  (N.1.subgroupOf E).map C.equiv.toMonoidHom

omit [E.Normal] in
theorem meetImage_normal (N : {N : Subgroup U // N.Normal}) :
    (C.meetImage N).Normal :=
  Subgroup.Normal.map inferInstance _ C.equiv.surjective

omit [E.Normal] in
theorem mem_meetImage (N : {N : Subgroup U // N.Normal})
    (y : (i : C.ι) → C.factor i) :
    y ∈ C.meetImage N ↔ ((C.equiv.symm y : E) : U) ∈ N.1 := by
  rw [meetImage, Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]

omit [E.Normal] in
/-- `N ∩ E` is the subproduct over its support. -/
theorem mem_iff (N : {N : Subgroup U // N.Normal}) (x : E) :
    (x : U) ∈ N.1 ↔ ∀ i ∉ C.support N, C.equiv x i = 1 := by
  classical
  have h := pi_normal_mem_iff C.simple C.centerless (C.meetImage N)
    (C.meetImage_normal N) (C.equiv x)
  rw [C.mem_meetImage, MulEquiv.symm_apply_apply] at h
  rw [h]
  apply forall_congr'
  intro i
  constructor
  · intro hi hsupp
    apply hi
    intro y hy
    by_contra hyi
    apply hsupp
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨C.equiv.symm y, (C.mem_meetImage N y).mp hy, ?_⟩
    rwa [MulEquiv.apply_symm_apply]
  · intro hi hall
    apply hi
    intro hsupp
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hsupp
    obtain ⟨z, hz, hzi⟩ := hsupp
    apply hzi
    apply hall
    rw [C.mem_meetImage, MulEquiv.symm_apply_apply]
    exact hz

omit [E.Normal] in
include C in
/-- An element of `E` central modulo `N` lies in `N`. -/
theorem mem_of_commutators (N : {N : Subgroup U // N.Normal}) (x : E)
    (hx : ∀ y : E, ((x * y * x⁻¹ * y⁻¹ : E) : U) ∈ N.1) : (x : U) ∈ N.1 := by
  classical
  have h := pi_mem_of_commutators_mem C.simple C.centerless (C.meetImage N)
    (C.meetImage_normal N) (C.equiv x) (by
      intro z
      rw [C.mem_meetImage]
      obtain ⟨y, rfl⟩ := C.equiv.surjective z
      have : C.equiv.symm (C.equiv x * C.equiv y * (C.equiv x)⁻¹ * (C.equiv y)⁻¹) =
          x * y * x⁻¹ * y⁻¹ := by
        rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
          MulEquiv.symm_apply_apply]
      rw [this]
      exact hx y)
  rwa [C.mem_meetImage, MulEquiv.symm_apply_apply] at h

/-- A normal subgroup is determined by its support and by `NE`. -/
theorem eq_of_support_eq (N N' : {N : Subgroup U // N.Normal})
    (hs : C.support N = C.support N') (hsup : N.1 ⊔ E = N'.1 ⊔ E) : N = N' := by
  have hmeet : ∀ (N N' : {N : Subgroup U // N.Normal}), C.support N = C.support N' →
      ∀ x : E, (x : U) ∈ N.1 → (x : U) ∈ N'.1 := by
    intro N N' hs x hx
    rw [C.mem_iff] at hx ⊢
    rwa [← hs]
  have hle : ∀ (N N' : {N : Subgroup U // N.Normal}), C.support N = C.support N' →
      N.1 ⊔ E = N'.1 ⊔ E → N.1 ≤ N'.1 := by
    intro N N' hs hsup n hn
    have hn' : n ∈ N'.1 ⊔ E := hsup ▸ (le_sup_left : N.1 ≤ N.1 ⊔ E) hn
    obtain ⟨n', hn'N, x, hxE, hnx⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := N'.1) (t := E)).mp hn'
    have hx : x ∈ N'.1 := by
      apply C.mem_of_commutators N' ⟨x, hxE⟩
      intro y
      have hxval : x = n'⁻¹ * n := by rw [← hnx]; group
      have ha : n * (y : U) * n⁻¹ * (y : U)⁻¹ ∈ N'.1 := by
        have haE : n * (y : U) * n⁻¹ * (y : U)⁻¹ ∈ E :=
          E.mul_mem (‹E.Normal›.conj_mem _ y.2 n) (E.inv_mem y.2)
        have haN : n * (y : U) * n⁻¹ * (y : U)⁻¹ ∈ N.1 := by
          have : n * (y : U) * n⁻¹ * (y : U)⁻¹ = n * ((y : U) * n⁻¹ * (y : U)⁻¹) := by
            group
          rw [this]
          exact N.1.mul_mem hn (N.2.conj_mem _ (N.1.inv_mem hn) y)
        exact hmeet N N' hs ⟨_, haE⟩ haN
      change x * (y : U) * x⁻¹ * (y : U)⁻¹ ∈ N'.1
      have hexp : x * (y : U) * x⁻¹ * (y : U)⁻¹ =
          (n'⁻¹ * (n * (y : U) * n⁻¹ * (y : U)⁻¹) * n') *
            (n'⁻¹ * ((y : U) * n' * (y : U)⁻¹)) := by
        rw [hxval]
        group
      rw [hexp]
      exact N'.1.mul_mem (by
          have := N'.2.conj_mem _ ha n'⁻¹
          simpa using this)
        (N'.1.mul_mem (N'.1.inv_mem hn'N) (N'.2.conj_mem _ hn'N y))
    rw [← hnx]
    exact N'.1.mul_mem hn'N hx
  apply Subtype.ext
  exact le_antisymm (hle N N' hs hsup) (hle N' N hs.symm hsup.symm)

omit [E.Normal] in
include C in
/-- The image of `E` in `U/N` is centerless. -/
theorem image_centerless (N : {N : Subgroup U // N.Normal}) (c : U ⧸ N.1)
    (hc : c ∈ quotientImage E N) (hcomm : ∀ d ∈ quotientImage E N, c * d = d * c) :
    c = 1 := by
  obtain ⟨x, hx, rfl⟩ := hc
  apply (QuotientGroup.eq_one_iff x).mpr
  apply C.mem_of_commutators N ⟨x, hx⟩
  intro y
  apply (QuotientGroup.eq_one_iff _).mp
  have := hcomm (QuotientGroup.mk' N.1 y) ⟨y, y.2, rfl⟩
  change (x : U ⧸ N.1) * (y : U ⧸ N.1) * (x : U ⧸ N.1)⁻¹ * (y : U ⧸ N.1)⁻¹ = 1
  change (x : U ⧸ N.1) * (y : U ⧸ N.1) = (y : U ⧸ N.1) * (x : U ⧸ N.1) at this
  rw [this]
  group


/-- The quotient map of `E` onto its image in `U/N`. -/
def imageMap (N : {N : Subgroup U // N.Normal}) : E →* quotientImage E N :=
  (QuotientGroup.mk' N.1).subgroupMap E

omit [E.Normal] in
theorem imageMap_surjective (N : {N : Subgroup U // N.Normal}) :
    Function.Surjective (imageMap (E := E) N) :=
  MonoidHom.subgroupMap_surjective _ _

omit [E.Normal] in
theorem imageMap_eq_one_iff (N : {N : Subgroup U // N.Normal}) (x : E) :
    imageMap N x = 1 ↔ (x : U) ∈ N.1 := by
  rw [← (QuotientGroup.eq_one_iff (x : U))]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

/-- Projection of the image of `E` to one simple factor outside the
support. -/
def projection (N : {N : Subgroup U // N.Normal}) (i : C.ι)
    (hi : i ∉ C.support N) : quotientImage E N →* C.factor i :=
  (QuotientGroup.lift (imageMap N).ker
      ((Pi.evalMonoidHom C.factor i).comp C.equiv.toMonoidHom) (by
        intro x hx
        rw [MonoidHom.mem_ker] at hx ⊢
        rw [imageMap_eq_one_iff, C.mem_iff] at hx
        exact hx i hi)).comp
    (QuotientGroup.quotientKerEquivOfSurjective (imageMap N)
      (imageMap_surjective N)).symm.toMonoidHom

omit [E.Normal] in
theorem projection_imageMap (N : {N : Subgroup U // N.Normal}) (i : C.ι)
    (hi : i ∉ C.support N) (x : E) :
    C.projection N i hi (imageMap N x) = C.equiv x i := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective (imageMap N)
      (imageMap_surjective N)).symm (imageMap N x) =
      (QuotientGroup.mk x : E ⧸ (imageMap N).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [projection, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h,
    QuotientGroup.lift_mk]
  rfl

omit [E.Normal] in
theorem projection_surjective (N : {N : Subgroup U // N.Normal}) (i : C.ι)
    (hi : i ∉ C.support N) : Function.Surjective (C.projection N i hi) := by
  intro s
  refine ⟨imageMap N (C.equiv.symm (Pi.mulSingle i s)), ?_⟩
  rw [projection_imageMap, MulEquiv.apply_symm_apply, Pi.mulSingle_eq_same]

omit [E.Normal] in
theorem projections_injective (N : {N : Subgroup U // N.Normal})
    (c : quotientImage E N)
    (hc : ∀ i (hi : i ∉ C.support N), C.projection N i hi c = 1) : c = 1 := by
  obtain ⟨x, rfl⟩ := imageMap_surjective N c
  rw [imageMap_eq_one_iff, C.mem_iff]
  intro i hi
  rw [← C.projection_imageMap N i hi]
  exact hc i hi

omit [E.Normal] in
/-- Onto maps to the image of `E`: at most the product over the simple
factors outside the support. -/
theorem imageEpi_card_le (N : {N : Subgroup U // N.Normal}) {F : Type*}
    [Group F] [Finite F] :
    Nat.card (GroupEpimorphism F (quotientImage E N)) ≤
      ∏ i ∈ Finset.univ \ C.support N,
        Nat.card (GroupEpimorphism F (C.factor i)) := by
  let s := Finset.univ \ C.support N
  have hs : ∀ i : s, i.1 ∉ C.support N := fun i => (Finset.mem_sdiff.mp i.2).2
  let π : GroupEpimorphism F (quotientImage E N) →
      ((i : s) → GroupEpimorphism F (C.factor i)) := fun ρ i =>
    ⟨(C.projection N i (hs i)).comp ρ.1,
      (C.projection_surjective N i (hs i)).comp ρ.2⟩
  have hπ : Function.Injective π := by
    intro ρ ρ' h
    apply Subtype.ext
    ext1 f
    have hc : (ρ.1 f)⁻¹ * ρ'.1 f = 1 := by
      apply C.projections_injective N
      intro i hi
      have := congrArg (fun g : GroupEpimorphism F (C.factor i) => g.1 f)
        (congrFun h ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩⟩)
      simp only [π, MonoidHom.comp_apply] at this
      rw [map_mul, map_inv, this, inv_mul_cancel]
    exact (inv_mul_eq_one.mp hc)
  letI : ∀ i, Finite (GroupEpimorphism F (C.factor i)) := fun i =>
    Finite.of_injective (fun g : GroupEpimorphism F (C.factor i) =>
      (g.1 : F → C.factor i)) (fun _ _ hg => Subtype.ext (DFunLike.coe_injective hg))
  have hcard := Nat.card_le_card_of_injective π hπ
  rw [Nat.card_pi] at hcard
  calc Nat.card (GroupEpimorphism F (quotientImage E N))
      ≤ ∏ i : s, Nat.card (GroupEpimorphism F (C.factor i)) := hcard
    _ = ∏ i ∈ s, Nat.card (GroupEpimorphism F (C.factor i)) :=
        Finset.prod_coe_sort s (fun i => Nat.card (GroupEpimorphism F (C.factor i)))

omit [E.Normal] in
/-- The same product with the simple-factor weights. -/
theorem imageEpi_card_le_weight (N : {N : Subgroup U // N.Normal}) {F : Type*}
    [Group F] [Finite F] (L : ℝ) (hL : Real.logb 2 (Nat.card F) ≤ L) :
    (Nat.card (GroupEpimorphism F (quotientImage E N)) : ℝ) ≤
      ∏ i ∈ Finset.univ \ C.support N, C.factorWeight L i := by
  have h : (Nat.card (GroupEpimorphism F (quotientImage E N)) : ℝ) ≤
      ∏ i ∈ Finset.univ \ C.support N,
        (Nat.card (GroupEpimorphism F (C.factor i)) : ℝ) := by
    exact_mod_cast C.imageEpi_card_le N (F := F)
  refine h.trans ?_
  apply Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _)
  intro i _
  exact (simpleGroupEpimorphism_card_le (C.simple i) (C.centerless i)).trans
    (C.factorWeight_mono hL i)

include C in
/-- An onto map to `U/N` is determined by its outer map and its restriction
onto the centerless image of `E`. -/
theorem fibre_card_le [Finite U] (N : {N : Subgroup U // N.Normal}) {J : Type*} [Group J]
    [Finite J] (θ : GroupEpimorphism J (U ⧸ (N.1 ⊔ E))) :
    Nat.card {φ : GroupEpimorphism J (U ⧸ N.1) //
        (quotientOuter E N).comp φ.1 = θ.1} ≤
      Nat.card (GroupEpimorphism θ.1.ker (quotientImage E N)) := by
  let ρ : {φ : GroupEpimorphism J (U ⧸ N.1) //
      (quotientOuter E N).comp φ.1 = θ.1} →
      GroupEpimorphism θ.1.ker (quotientImage E N) := fun φ =>
    ⟨{ toFun := fun y => ⟨φ.1.1 y, mem_quotientImage_of_outer E N _ (by
          have := DFunLike.congr_fun φ.2 (y : J)
          simp only [MonoidHom.comp_apply] at this
          rw [this]
          exact y.2)⟩
       map_one' := Subtype.ext (by simp)
       map_mul' := fun y y' => Subtype.ext (by simp) }, by
      rintro ⟨c, hc⟩
      obtain ⟨g, hg⟩ := φ.1.2 c
      have hgker : g ∈ θ.1.ker := by
        rw [MonoidHom.mem_ker]
        have := DFunLike.congr_fun φ.2 g
        simp only [MonoidHom.comp_apply] at this
        rw [← this, hg]
        exact quotientOuter_image E N c hc
      exact ⟨⟨g, hgker⟩, Subtype.ext hg⟩⟩
  have hρ : Function.Injective ρ := by
    intro φ φ' h
    apply Subtype.ext
    apply Subtype.ext
    ext1 g
    -- the difference lies in the image and centralizes it
    let c := (φ'.1.1 g)⁻¹ * φ.1.1 g
    have hcE : c ∈ quotientImage E N := by
      apply mem_quotientImage_of_outer
      have h1 := DFunLike.congr_fun φ.2 g
      have h2 := DFunLike.congr_fun φ'.2 g
      simp only [MonoidHom.comp_apply] at h1 h2
      simp only [c, map_mul, map_inv, h1, h2, inv_mul_cancel]
    have hy : ∀ y : θ.1.ker, φ.1.1 y = φ'.1.1 y := fun y =>
      congrArg Subtype.val (DFunLike.congr_fun (congrArg Subtype.val h) y)
    have hcomm : ∀ d ∈ quotientImage E N, c * d = d * c := by
      intro d hd
      obtain ⟨y, hyd⟩ := (ρ φ).2 ⟨d, hd⟩
      have hyd' : φ.1.1 y = d := congrArg Subtype.val hyd
      have hconj : g * (y : J) * g⁻¹ ∈ θ.1.ker := θ.1.normal_ker.conj_mem _ y.2 g
      have h1 := hy ⟨_, hconj⟩
      simp only [map_mul, map_inv] at h1
      rw [hy y] at h1
      rw [← hyd', hy y]
      simp only [c]
      calc (φ'.1.1 g)⁻¹ * φ.1.1 g * φ'.1.1 y
          = (φ'.1.1 g)⁻¹ * (φ.1.1 g * φ'.1.1 y * (φ.1.1 g)⁻¹) * φ.1.1 g := by group
        _ = (φ'.1.1 g)⁻¹ * (φ'.1.1 g * φ'.1.1 y * (φ'.1.1 g)⁻¹) * φ.1.1 g := by
            rw [h1]
        _ = φ'.1.1 y * ((φ'.1.1 g)⁻¹ * φ.1.1 g) := by group
    have := C.image_centerless N c hcE hcomm
    exact (inv_mul_eq_one.mp this).symm
  letI : Finite (GroupEpimorphism θ.1.ker (quotientImage E N)) :=
    Finite.of_injective (fun g : GroupEpimorphism θ.1.ker (quotientImage E N) =>
      (g.1 : θ.1.ker → quotientImage E N))
      (fun _ _ hg => Subtype.ext (DFunLike.coe_injective hg))
  exact Nat.card_le_card_of_injective ρ hρ


theorem quotientOuter_surjective (N : {N : Subgroup U // N.Normal}) :
    Function.Surjective (quotientOuter E N) := by
  intro q
  induction q using QuotientGroup.induction_on with | H u => ?_
  exact ⟨(u : U ⧸ N.1), rfl⟩

/-- One literal axis:
`|Epi(J, U/N)| ≤ |Epi(J, U/NE)| · ∏_{i ∉ supp N} |Aut Sᵢ| log|J| / log|Sᵢ|`. -/
theorem axis_epi_le [Finite U] (N : {N : Subgroup U // N.Normal}) {J : Type*}
    [Group J] [Finite J] :
    (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ) ≤
      Nat.card (GroupEpimorphism J (U ⧸ (N.1 ⊔ E))) *
        ∏ i ∈ Finset.univ \ C.support N,
          C.factorWeight (Real.logb 2 (Nat.card J)) i := by
  let π : GroupEpimorphism J (U ⧸ N.1) → GroupEpimorphism J (U ⧸ (N.1 ⊔ E)) :=
    fun φ => ⟨(quotientOuter E N).comp φ.1, (quotientOuter_surjective N).comp φ.2⟩
  letI : Finite (GroupEpimorphism J (U ⧸ N.1)) := Finite.of_injective
    (fun φ : GroupEpimorphism J (U ⧸ N.1) => (φ.1 : J → U ⧸ N.1))
    (fun _ _ h => Subtype.ext (DFunLike.coe_injective h))
  letI : Finite (GroupEpimorphism J (U ⧸ (N.1 ⊔ E))) := Finite.of_injective
    (fun φ : GroupEpimorphism J (U ⧸ (N.1 ⊔ E)) => (φ.1 : J → U ⧸ (N.1 ⊔ E)))
    (fun _ _ h => Subtype.ext (DFunLike.coe_injective h))
  letI := Fintype.ofFinite (GroupEpimorphism J (U ⧸ (N.1 ⊔ E)))
  let W : ℝ := ∏ i ∈ Finset.univ \ C.support N,
    C.factorWeight (Real.logb 2 (Nat.card J)) i
  have hfib : ∀ θ, (Nat.card {φ // π φ = θ} : ℝ) ≤ W := by
    intro θ
    have h1 : Nat.card {φ // π φ = θ} ≤
        Nat.card {φ : GroupEpimorphism J (U ⧸ N.1) //
          (quotientOuter E N).comp φ.1 = θ.1} :=
      Nat.card_le_card_of_injective
        (fun φ => ⟨φ.1, congrArg Subtype.val φ.2⟩)
        (fun φ φ' h => by
          simp only [Subtype.mk.injEq] at h
          exact Subtype.ext h)
    have h2 := C.fibre_card_le N θ
    have hker : Real.logb 2 (Nat.card θ.1.ker) ≤ Real.logb 2 (Nat.card J) := by
      apply Real.logb_le_logb_of_le (by norm_num)
        (by exact_mod_cast Nat.card_pos)
      exact_mod_cast Subgroup.card_le_card_group θ.1.ker
    have h3 := C.imageEpi_card_le_weight N (F := θ.1.ker) _ hker
    calc (Nat.card {φ // π φ = θ} : ℝ)
        ≤ Nat.card (GroupEpimorphism θ.1.ker (quotientImage E N)) := by
          exact_mod_cast h1.trans h2
      _ ≤ W := h3
  calc (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ)
      = ∑ θ, (Nat.card {φ // π φ = θ} : ℝ) := by
        rw [← Nat.card_congr (Equiv.sigmaFiberEquiv π), Nat.card_sigma]
        push_cast
        rfl
    _ ≤ ∑ _θ : GroupEpimorphism J (U ⧸ (N.1 ⊔ E)), W :=
        Finset.sum_le_sum (fun θ _ => hfib θ)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Fintype.card_eq_nat_card]

/-- The semisimple outer fibre:
`∑_N |Epi(J, U/N)| ≤ Z_J(U/E) · ∏ᵢ (1 + |Aut Sᵢ| log|J| / log|Sᵢ|)`. -/
theorem outerSum_le [Finite U] {J : Type*} [Group J] [Finite J] :
    (∑ N : {N : Subgroup U // N.Normal},
        (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ)) ≤
      (∑ D : {D : Subgroup (U ⧸ E) // D.Normal},
          (Nat.card (GroupEpimorphism J ((U ⧸ E) ⧸ D.1)) : ℝ)) *
        C.outerFactor (Real.logb 2 (Nat.card J)) := by
  set L := Real.logb 2 (Nat.card J)
  have hL : 0 ≤ L := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast Nat.card_pos)
  let w : Finset C.ι → ℝ := fun T => ∏ i ∈ Finset.univ \ T, C.factorWeight L i
  have hw : ∀ T, 0 ≤ w T := fun T =>
    Finset.prod_nonneg (fun i _ => C.factorWeight_nonneg hL i)
  let D : {N : Subgroup U // N.Normal} → {D : Subgroup (U ⧸ E) // D.Normal} :=
    fun N => ⟨(N.1 ⊔ E).map (QuotientGroup.mk' E),
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective E)⟩
  let g : Finset C.ι × {D : Subgroup (U ⧸ E) // D.Normal} → ℝ := fun p =>
    (Nat.card (GroupEpimorphism J ((U ⧸ E) ⧸ p.2.1)) : ℝ) * w p.1
  have hg : ∀ p, 0 ≤ g p := fun p => mul_nonneg (Nat.cast_nonneg _) (hw p.1)
  let κ : {N : Subgroup U // N.Normal} → Finset C.ι × {D : Subgroup (U ⧸ E) // D.Normal} :=
    fun N => (C.support N, D N)
  have hκ : Function.Injective κ := by
    intro N N' h
    have hs : C.support N = C.support N' := congrArg Prod.fst h
    have hD : (N.1 ⊔ E).map (QuotientGroup.mk' E) =
        (N'.1 ⊔ E).map (QuotientGroup.mk' E) :=
      congrArg (fun p : Finset C.ι × {D : Subgroup (U ⧸ E) // D.Normal} => p.2.1) h
    have hsup : N.1 ⊔ E = N'.1 ⊔ E := by
      have h1 := congrArg (Subgroup.comap (QuotientGroup.mk' E)) hD
      rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
        sup_assoc, sup_idem, sup_assoc, sup_idem] at h1
      exact h1
    exact C.eq_of_support_eq N N' hs hsup
  have haxis : ∀ N : {N : Subgroup U // N.Normal},
      (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ) ≤ g (κ N) := by
    intro N
    have h := C.axis_epi_le N (J := J)
    have hcongr : Nat.card (GroupEpimorphism J (U ⧸ (N.1 ⊔ E))) =
        Nat.card (GroupEpimorphism J ((U ⧸ E) ⧸ (D N).1)) :=
      fusionGroupEpimorphism_card_congr (MulEquiv.refl J)
        (QuotientGroup.quotientQuotientEquivQuotient E (N.1 ⊔ E) le_sup_right).symm
    rw [hcongr] at h
    exact h
  calc (∑ N : {N : Subgroup U // N.Normal},
        (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ))
      ≤ ∑ N : {N : Subgroup U // N.Normal}, g (κ N) :=
        Finset.sum_le_sum (fun N _ => haxis N)
    _ = ∑ p ∈ Finset.univ.image κ, g p := by
        rw [Finset.sum_image (fun N _ N' _ h => hκ h)]
    _ ≤ ∑ p, g p :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun p _ _ => hg p)
    _ = (∑ T : Finset C.ι, w T) *
          ∑ D : {D : Subgroup (U ⧸ E) // D.Normal},
            (Nat.card (GroupEpimorphism J ((U ⧸ E) ⧸ D.1)) : ℝ) := by
        rw [Fintype.sum_prod_type, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro T _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro D _
        simp only [g]
        ring
    _ = _ := by
        have hprod : C.outerFactor L = ∑ T : Finset C.ι, w T := by
          unfold outerFactor
          rw [Finset.prod_add (fun _ => (1 : ℝ)) (C.factorWeight L) Finset.univ,
            Finset.powerset_univ]
          apply Finset.sum_congr rfl
          intro T _
          simp [w]
        rw [hprod, mul_comm]

end SemisimpleNormalChart

end SymmetricSubgroupAsymptotics
