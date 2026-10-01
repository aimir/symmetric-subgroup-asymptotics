import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting irreducible members of one common head

Let a group `G` act linearly on a finite-dimensional vector space `E` over a
finite field.  Consider a finite family `X` of invariant subspaces, each
irreducible of the same dimension `m`, and each containing a nonzero vector
`a` whose stabilizer fixes at most `q` vectors of the member.  The last
condition bounds the equivariant endomorphisms of the member by `q` (they are
determined by the image of `a`).

Then `|X| ≤ 1 + q + ⋯ + q^k` whenever `dim E < (k+1) m`.

The proof removes one member `W₁` and passes to `E / W₁`.  Distinct remaining
members meet `W₁` trivially; two members with the same image are graphs of an
equivariant map into `W₁`, and Schur's lemma bounds such maps by `q`.  The
members are counted inside one common space, so distinct isomorphism types
share one dimension budget.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DerivedHead

universe u v w

variable {K : Type v} [Field K] {G : Type w} [Group G]

/-- An invariant subspace. -/
def Invariant {E : Type u} [AddCommGroup E] [Module K E] (ρ : Representation K G E)
    (W : Submodule K E) : Prop :=
  ∀ g : G, ∀ x ∈ W, ρ g x ∈ W

/-- An irreducible invariant subspace of dimension `m` with a vector whose
stabilizer fixes at most `q` of its vectors. -/
structure HeadMember {E : Type u} [AddCommGroup E] [Module K E]
    (ρ : Representation K G E) (m q : ℕ) (W : Submodule K E) : Prop where
  invariant : Invariant ρ W
  ne_bot : W ≠ ⊥
  irreducible : ∀ W' : Submodule K E, W' ≤ W → Invariant ρ W' → W' = ⊥ ∨ W' = W
  finrank_eq : Module.finrank K W = m
  witness : ∃ a ∈ W, a ≠ 0 ∧
    Nat.card {x : W // ∀ g : G, ρ g a = a → ρ g (x : E) = x} ≤ q

section Ambient

variable {E : Type u} [AddCommGroup E] [Module K E] (ρ : Representation K G E)

/-- Distinct members meet trivially. -/
theorem HeadMember.inf_eq_bot {m q : ℕ} {W W₁ : Submodule K E}
    (hW : HeadMember ρ m q W) (hW₁ : HeadMember ρ m q W₁) (hne : W ≠ W₁) :
    W ⊓ W₁ = ⊥ := by
  have hinv : Invariant ρ (W ⊓ W₁) := fun g x hx =>
    ⟨hW.invariant g x hx.1, hW₁.invariant g x hx.2⟩
  rcases hW.irreducible _ inf_le_left hinv with h | h
  · exact h
  · exfalso
    have hle : W ≤ W₁ := by
      rw [← h]
      exact inf_le_right
    rcases hW₁.irreducible W hle hW.invariant with h' | h'
    · exact hW.ne_bot h'
    · exact hne h'

/-- Equivariant linear maps from one member into another. -/
def GHom (W₀ W₁ : Submodule K E) : Set (W₀ →ₗ[K] E) :=
  {f | (∀ x, f x ∈ W₁) ∧
    ∀ (g : G) (x : W₀) (hx : ρ g x ∈ W₀), f ⟨ρ g x, hx⟩ = ρ g (f x)}

theorem GHom.sub_mem {W₀ W₁ : Submodule K E} {f f' : W₀ →ₗ[K] E}
    (hf : f ∈ GHom ρ W₀ W₁) (hf' : f' ∈ GHom ρ W₀ W₁) : f - f' ∈ GHom ρ W₀ W₁ := by
  refine ⟨fun x => W₁.sub_mem (hf.1 x) (hf'.1 x), fun g x hx => ?_⟩
  simp only [LinearMap.sub_apply, hf.2 g x hx, hf'.2 g x hx, map_sub]

/-- The kernel of an equivariant map, as an invariant subspace of the member. -/
def GHom.kerSub {W₀ : Submodule K E} (f : W₀ →ₗ[K] E) : Submodule K E :=
  (LinearMap.ker f).map W₀.subtype

theorem GHom.kerSub_le {W₀ : Submodule K E} (f : W₀ →ₗ[K] E) : GHom.kerSub f ≤ W₀ := by
  rintro _ ⟨x, _, rfl⟩
  exact x.2

theorem GHom.kerSub_invariant {W₀ W₁ : Submodule K E} (hW₀ : Invariant ρ W₀)
    {f : W₀ →ₗ[K] E} (hf : f ∈ GHom ρ W₀ W₁) : Invariant ρ (GHom.kerSub f) := by
  rintro g _ ⟨x, hx, rfl⟩
  refine ⟨⟨ρ g x, hW₀ g x x.2⟩, ?_, rfl⟩
  have hx' : f x = 0 := hx
  show f ⟨ρ g x, hW₀ g x x.2⟩ = 0
  rw [hf.2 g x (hW₀ g x x.2), hx', map_zero]

/-- A member vanishing at one nonzero vector vanishes. -/
theorem GHom.eq_zero_of_apply {m q : ℕ} {W₀ W₁ : Submodule K E}
    (hW₀ : HeadMember ρ m q W₀) {f : W₀ →ₗ[K] E} (hf : f ∈ GHom ρ W₀ W₁)
    (a : W₀) (ha : (a : E) ≠ 0) (hfa : f a = 0) : f = 0 := by
  rcases hW₀.irreducible _ (GHom.kerSub_le f) (GHom.kerSub_invariant ρ hW₀.invariant hf)
    with h | h
  · exfalso
    have hmem : (a : E) ∈ GHom.kerSub f := ⟨a, hfa, rfl⟩
    rw [h] at hmem
    exact ha ((Submodule.mem_bot K).mp hmem)
  · ext x
    have hx : (x : E) ∈ GHom.kerSub f := by
      rw [h]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext hyx
    rw [← this]
    simpa using hy

variable [Finite K] [FiniteDimensional K E]

theorem one_le_of_witness {m q : ℕ} {W : Submodule K E} (hW : HeadMember ρ m q W) :
    1 ≤ q := by
  haveI : Finite E := Module.finite_of_finite K
  obtain ⟨a, _, _, hcard⟩ := hW.witness
  have hpos : 0 < Nat.card {x : W // ∀ g : G, ρ g a = a → ρ g (x : E) = x} :=
    Nat.card_pos_iff.mpr ⟨⟨(⟨⟨0, W.zero_mem⟩, fun g _ => by simp⟩ :
      {x : W // ∀ g : G, ρ g a = a → ρ g (x : E) = x})⟩, inferInstance⟩
  omega

/-- **Schur bound.**  Equivariant maps between two members number at most `q`. -/
theorem GHom.card_le {m q : ℕ} {W₀ W₁ : Submodule K E}
    (hW₀ : HeadMember ρ m q W₀) (hW₁ : HeadMember ρ m q W₁) :
    Nat.card (GHom ρ W₀ W₁) ≤ q := by
  haveI : Finite E := Module.finite_of_finite K
  have hq := one_le_of_witness ρ hW₀
  letI : Finite (W₀ →ₗ[K] E) := Module.finite_of_finite K
  by_cases hall : ∀ f ∈ GHom ρ W₀ W₁, f = 0
  · have : Nat.card (GHom ρ W₀ W₁) ≤ 1 := by
      rw [Finite.card_le_one_iff_subsingleton]
      constructor
      rintro ⟨f, hf⟩ ⟨f', hf'⟩
      apply Subtype.ext
      show f = f'
      rw [hall f hf, hall f' hf']
    omega
  rw [not_forall] at hall
  obtain ⟨f₀, hall⟩ := hall
  rw [_root_.not_imp] at hall
  obtain ⟨hf₀, hf₀ne⟩ := hall
  -- `f₀` is injective
  have hker : GHom.kerSub f₀ = ⊥ := by
    rcases hW₀.irreducible _ (GHom.kerSub_le f₀)
        (GHom.kerSub_invariant ρ hW₀.invariant hf₀) with h | h
    · exact h
    · exfalso
      apply hf₀ne
      ext x
      have hx : (x : E) ∈ GHom.kerSub f₀ := by
        rw [h]
        exact x.2
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := Subtype.ext hyx
      rw [← this]
      simpa using hy
  have hinj : Function.Injective f₀ := by
    rw [← LinearMap.ker_eq_bot]
    rw [eq_bot_iff] at hker ⊢
    intro x hx
    have : (x : E) ∈ GHom.kerSub f₀ := ⟨x, hx, rfl⟩
    have h0 := (Submodule.mem_bot K).mp (hker this)
    exact (Submodule.mem_bot K).mpr (Subtype.ext h0)
  -- `f₀` is onto `W₁`
  have hrange : LinearMap.range f₀ = W₁ := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨x, rfl⟩
      exact hf₀.1 x
    · rw [LinearMap.finrank_range_of_inj hinj, hW₀.finrank_eq, hW₁.finrank_eq]
  obtain ⟨a, ha, ha0, hacard⟩ := hW₀.witness
  -- maps are determined by their value at `a`
  let T : Type _ := {y : W₁ // ∀ g : G, ρ g a = a → ρ g (y : E) = y}
  let S : Type _ := {x : W₀ // ∀ g : G, ρ g a = a → ρ g (x : E) = x}
  let ev : GHom ρ W₀ W₁ → T := fun f => ⟨⟨f.1 ⟨a, ha⟩, f.2.1 _⟩, fun g hg => by
    have hx : ρ g (⟨a, ha⟩ : W₀) ∈ W₀ := by
      change ρ g a ∈ W₀
      rw [hg]
      exact ha
    have := f.2.2 g ⟨a, ha⟩ hx
    have e : (⟨ρ g ((⟨a, ha⟩ : W₀) : E), hx⟩ : W₀) = ⟨a, ha⟩ := Subtype.ext hg
    rw [e] at this
    exact this.symm⟩
  have hev : Function.Injective ev := by
    intro f f' hff
    have h1 : f.1 ⟨a, ha⟩ = f'.1 ⟨a, ha⟩ := congrArg (fun y : T => ((y.1 : W₁) : E)) hff
    have hsub := GHom.sub_mem ρ f.2 f'.2
    have h0 := GHom.eq_zero_of_apply ρ hW₀ hsub ⟨a, ha⟩ ha0 (by
      rw [LinearMap.sub_apply, h1, sub_self])
    exact Subtype.ext (sub_eq_zero.mp h0)
  -- the fixed vectors of `W₁` come from those of `W₀`
  have hrng : ∀ y : T, ∃ x : W₀, f₀ x = (y.1 : E) := fun y =>
    LinearMap.mem_range.mp (by rw [hrange]; exact y.1.2)
  let back : T → S := fun y => Subtype.mk (Classical.choose (hrng y)) (fun g hg => by
      have hspec := Classical.choose_spec (hrng y)
      have hx : ρ g ((Classical.choose (hrng y) : W₀) : E) ∈ W₀ :=
        hW₀.invariant g _ (Classical.choose (hrng y)).2
      have := hf₀.2 g (Classical.choose (hrng y)) hx
      have key : f₀ ⟨ρ g ((Classical.choose (hrng y) : W₀) : E), hx⟩ =
          f₀ (Classical.choose (hrng y)) := by
        calc f₀ ⟨ρ g ((Classical.choose (hrng y) : W₀) : E), hx⟩
            = ρ g (f₀ (Classical.choose (hrng y))) := this
          _ = ρ g (y.1 : E) := by rw [hspec]
          _ = (y.1 : E) := y.2 g hg
          _ = f₀ (Classical.choose (hrng y)) := hspec.symm
      exact congrArg Subtype.val (hinj key))
  have hback : Function.Injective back := by
    intro y y' hyy
    have h1 := congrArg (fun s : S => f₀ s.1) hyy
    simp only [back] at h1
    have e1 := Classical.choose_spec (hrng y)
    have e2 := Classical.choose_spec (hrng y')
    apply Subtype.ext
    apply Subtype.ext
    rw [← e1, ← e2]
    exact h1
  haveI : Finite E := Module.finite_of_finite K
  letI : Finite T := inferInstance
  letI : Finite S := inferInstance
  calc Nat.card (GHom ρ W₀ W₁) ≤ Nat.card T := Nat.card_le_card_of_injective ev hev
    _ ≤ Nat.card S := Nat.card_le_card_of_injective back hback
    _ ≤ q := hacard

end Ambient

/-! ## Passing to the quotient by one member -/

section Quotient

variable {E : Type u} [AddCommGroup E] [Module K E] (ρ : Representation K G E)

/-- The action on the quotient by an invariant subspace. -/
def quotientRep (W₁ : Submodule K E) (h : Invariant ρ W₁) :
    Representation K G (E ⧸ W₁) where
  toFun g := W₁.mapQ W₁ (ρ g) (fun x hx => h g x hx)
  map_one' := by
    apply Submodule.linearMap_qext
    ext x
    simp
  map_mul' g g' := by
    apply Submodule.linearMap_qext
    ext x
    simp

theorem quotientRep_mk (W₁ : Submodule K E) (h : Invariant ρ W₁) (g : G) (x : E) :
    quotientRep ρ W₁ h g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ g x) := rfl

/-- The image of a member meeting `W₁` trivially is a member of the quotient. -/
theorem HeadMember.map_mkQ [Finite K] [FiniteDimensional K E] {m q : ℕ}
    {W W₁ : Submodule K E} (h₁ : Invariant ρ W₁)
    (hW : HeadMember ρ m q W) (hdisj : W ⊓ W₁ = ⊥) :
    HeadMember (quotientRep ρ W₁ h₁) m q (W.map W₁.mkQ) := by
  haveI : Finite E := Module.finite_of_finite K
  have hzero : ∀ y ∈ W, Submodule.Quotient.mk (p := W₁) y = 0 → y = 0 := by
    intro y hy h0
    have hy1 : y ∈ W₁ := (Submodule.Quotient.mk_eq_zero W₁).mp h0
    have : y ∈ W ⊓ W₁ := ⟨hy, hy1⟩
    rw [hdisj] at this
    exact (Submodule.mem_bot K).mp this
  have hinjW : ∀ y ∈ W, ∀ y' ∈ W,
      Submodule.Quotient.mk (p := W₁) y = Submodule.Quotient.mk y' → y = y' := by
    intro y hy y' hy' h
    have := hzero (y - y') (W.sub_mem hy hy') (by
      rw [Submodule.Quotient.mk_sub, h, sub_self])
    exact sub_eq_zero.mp this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro g _ ⟨y, hy, rfl⟩
    exact ⟨ρ g y, hW.invariant g y hy, rfl⟩
  · intro hbot
    apply hW.ne_bot
    rw [eq_bot_iff]
    intro y hy
    have : W₁.mkQ y ∈ W.map W₁.mkQ := ⟨y, hy, rfl⟩
    rw [hbot] at this
    exact (Submodule.mem_bot K).mpr (hzero y hy ((Submodule.mem_bot K).mp this))
  · intro W'' hle hinv
    let W3 : Submodule K E := W ⊓ W''.comap W₁.mkQ
    have hinv3 : Invariant ρ W3 := by
      intro g y hy
      refine ⟨hW.invariant g y hy.1, ?_⟩
      have := hinv g _ hy.2
      simpa [Submodule.mem_comap, quotientRep_mk] using this
    rcases hW.irreducible W3 inf_le_left hinv3 with h3 | h3
    · left
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨y, hy, rfl⟩ := hle hz
      have hy3 : y ∈ W3 := ⟨hy, hz⟩
      rw [h3] at hy3
      rw [(Submodule.mem_bot K).mp hy3, map_zero]
      exact Submodule.zero_mem _
    · right
      apply le_antisymm hle
      rintro _ ⟨y, hy, rfl⟩
      have : y ∈ W3 := by
        rw [h3]
        exact hy
      exact this.2
  · have hmap : W.map W₁.mkQ = LinearMap.range (W₁.mkQ.comp W.subtype) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    rw [hmap, LinearMap.finrank_range_of_inj, hW.finrank_eq]
    intro y y' h
    exact Subtype.ext (hinjW y y.2 y' y'.2 h)
  · obtain ⟨a, ha, ha0, hacard⟩ := hW.witness
    refine ⟨W₁.mkQ a, ⟨a, ha, rfl⟩, fun h0 => ha0 (hzero a ha h0), ?_⟩
    let back : {x : W.map W₁.mkQ //
        ∀ g : G, quotientRep ρ W₁ h₁ g (W₁.mkQ a) = W₁.mkQ a →
          quotientRep ρ W₁ h₁ g (x : E ⧸ W₁) = x} →
        {x : W // ∀ g : G, ρ g a = a → ρ g (x : E) = x} := fun x =>
      ⟨⟨Classical.choose x.1.2, (Classical.choose_spec x.1.2).1⟩, fun g hg => by
        have hspec := Classical.choose_spec x.1.2
        have hfix := x.2 g (by rw [Submodule.mkQ_apply, quotientRep_mk, hg])
        apply hinjW _ (hW.invariant g _ hspec.1) _ hspec.1
        have h2 : Submodule.Quotient.mk (p := W₁) (Classical.choose x.1.2) =
            (x.1 : E ⧸ W₁) := hspec.2
        rw [← quotientRep_mk ρ W₁ h₁, h2]
        exact hfix⟩
    have hback : Function.Injective back := by
      intro x x' hxx
      have h1 := congrArg (fun s : {x : W // ∀ g : G, ρ g a = a → ρ g (x : E) = x} =>
        Submodule.Quotient.mk (p := W₁) (s.1 : E)) hxx
      simp only [back] at h1
      have e1 : Submodule.Quotient.mk (p := W₁) (Classical.choose x.1.2) =
          (x.1 : E ⧸ W₁) := (Classical.choose_spec x.1.2).2
      have e2 : Submodule.Quotient.mk (p := W₁) (Classical.choose x'.1.2) =
          (x'.1 : E ⧸ W₁) := (Classical.choose_spec x'.1.2).2
      apply Subtype.ext
      apply Subtype.ext
      rw [← e1, ← e2]
      exact h1
    exact (Nat.card_le_card_of_injective back hback).trans hacard

/-- Two members with the same image modulo `W₁` differ by the graph of an
equivariant map into `W₁`. -/
theorem graph_exists {W₀ W W₁ : Submodule K E} (h₁ : Invariant ρ W₁)
    (hW : Invariant ρ W) (hdisj : W ⊓ W₁ = ⊥)
    (hmap : W.map W₁.mkQ = W₀.map W₁.mkQ) :
    ∃ h ∈ GHom ρ W₀ W₁, ∀ y : E, y ∈ W ↔ ∃ x : W₀, y = x + h x := by
  have hex : ∀ x : W₀, ∃ y ∈ W, y - x ∈ W₁ := by
    intro x
    have hx : W₁.mkQ x ∈ W₀.map W₁.mkQ := ⟨x, x.2, rfl⟩
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    exact ⟨y, hy, (Submodule.Quotient.eq W₁).mp hyx⟩
  let σ : W₀ → E := fun x => Classical.choose (hex x)
  have hσ : ∀ x, σ x ∈ W ∧ σ x - x ∈ W₁ := fun x => Classical.choose_spec (hex x)
  have huniq : ∀ (x : W₀) (y : E), y ∈ W → y - x ∈ W₁ → σ x = y := by
    intro x y hy hyx
    have hd : σ x - y ∈ W ⊓ W₁ := by
      refine ⟨W.sub_mem (hσ x).1 hy, ?_⟩
      have := W₁.sub_mem (hσ x).2 hyx
      simpa using this
    rw [hdisj] at hd
    exact sub_eq_zero.mp ((Submodule.mem_bot K).mp hd)
  let hlin : W₀ →ₗ[K] E :=
    { toFun := fun x => σ x - x
      map_add' := by
        intro x x'
        have : σ (x + x') = σ x + σ x' := huniq _ _ (W.add_mem (hσ x).1 (hσ x').1) (by
          have := W₁.add_mem (hσ x).2 (hσ x').2
          rw [Submodule.coe_add]
          convert this using 1
          abel)
        rw [this, Submodule.coe_add]
        abel
      map_smul' := by
        intro c x
        have : σ (c • x) = c • σ x := huniq _ _ (W.smul_mem c (hσ x).1) (by
          have := W₁.smul_mem c (hσ x).2
          rw [Submodule.coe_smul]
          convert this using 1
          rw [smul_sub])
        simp only [RingHom.id_apply]
        rw [this, Submodule.coe_smul, smul_sub] }
  refine ⟨hlin, ⟨fun x => (hσ x).2, fun g x hx => ?_⟩, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · change σ ⟨ρ g x, hx⟩ - ρ g x = ρ g (σ x - x)
    have : σ ⟨ρ g x, hx⟩ = ρ g (σ x) := huniq _ _ (hW g _ (hσ x).1) (by
      rw [← map_sub]
      exact h₁ g _ (hσ x).2)
    rw [this, map_sub]
  · have hy' : W₁.mkQ y ∈ W₀.map W₁.mkQ := by
      rw [← hmap]
      exact ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hy'
    refine ⟨⟨x, hx⟩, ?_⟩
    have : σ ⟨x, hx⟩ = y := huniq _ _ hy ((Submodule.Quotient.eq W₁).mp hxy.symm)
    change y = x + (σ ⟨x, hx⟩ - x)
    rw [this]
    abel
  · rintro ⟨x, rfl⟩
    change (x : E) + (σ x - x) ∈ W
    have : (x : E) + (σ x - x) = σ x := by abel
    rw [this]
    exact (hσ x).1

end Quotient

/-! ## The count -/

section Main

variable [Finite K]

/-- **The common-head count.**  A family of members in a space of dimension
less than `(k+1) m` has at most `1 + q + ⋯ + q^k` elements. -/
theorem card_family_le (m q : ℕ) :
    ∀ (k : ℕ) (E : Type u) [AddCommGroup E] [Module K E] [FiniteDimensional K E]
      (ρ : Representation K G E) (X : Finset (Submodule K E)),
      (∀ W ∈ X, HeadMember ρ m q W) → Module.finrank K E < (k + 1) * m →
      X.card ≤ ∑ j ∈ Finset.range (k + 1), q ^ j := by
  intro k
  induction k with
  | zero =>
    intro E _ _ _ ρ X hX hdim
    have hXe : X = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro W hW
      have h1 := (hX W hW).finrank_eq
      have h2 := Submodule.finrank_le W
      omega
    simp [hXe]
  | succ k ih =>
    intro E _ _ _ ρ X hX hdim
    rcases X.eq_empty_or_nonempty with hXe | ⟨W₁, hW₁X⟩
    · simp [hXe]
    have hW₁ := hX W₁ hW₁X
    let f : Submodule K E → Submodule K (E ⧸ W₁) := fun W => W.map W₁.mkQ
    let Y := X.erase W₁
    have hY : ∀ W ∈ Y, HeadMember ρ m q W ∧ W ⊓ W₁ = ⊥ := by
      intro W hW
      have hWX := Finset.mem_of_mem_erase hW
      have hne := Finset.ne_of_mem_erase hW
      exact ⟨hX W hWX, (hX W hWX).inf_eq_bot ρ hW₁ hne⟩
    have hdim' : Module.finrank K (E ⧸ W₁) < (k + 1) * m := by
      have h1 := Submodule.finrank_quotient_add_finrank W₁
      rw [hW₁.finrank_eq] at h1
      have h2 : (k + 1 + 1) * m = (k + 1) * m + m := by ring
      omega
    have hIH := ih (E ⧸ W₁) (quotientRep ρ W₁ hW₁.invariant) (Y.image f) (by
      intro W' hW'
      obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hW'
      exact (hY W hW).1.map_mkQ ρ hW₁.invariant (hY W hW).2) hdim'
    have hfib : Y.card ≤ q * (Y.image f).card := by
      apply Finset.card_le_mul_card_image
      intro W' hW'
      obtain ⟨W₀, hW₀, hW₀f⟩ := Finset.mem_image.mp hW'
      have hgraph : ∀ W ∈ Y.filter (fun W => f W = W'),
          ∃ h ∈ GHom ρ W₀ W₁, ∀ y : E, y ∈ W ↔ ∃ x : W₀, y = x + h x := by
        intro W hW
        rw [Finset.mem_filter] at hW
        refine graph_exists ρ hW₁.invariant (hY W hW.1).1.invariant (hY W hW.1).2 ?_
        exact hW.2.trans hW₀f.symm
      letI : Finite (W₀ →ₗ[K] E) := Module.finite_of_finite K
      let enc : (Y.filter (fun W => f W = W')) → GHom ρ W₀ W₁ := fun W =>
        ⟨Classical.choose (hgraph W.1 W.2), (Classical.choose_spec (hgraph W.1 W.2)).1⟩
      have henc : Function.Injective enc := by
        intro W W'' he
        have he' : Classical.choose (hgraph W.1 W.2) = Classical.choose (hgraph W''.1 W''.2) :=
          congrArg Subtype.val he
        apply Subtype.ext
        ext y
        rw [(Classical.choose_spec (hgraph W.1 W.2)).2 y,
          (Classical.choose_spec (hgraph W''.1 W''.2)).2 y, he']
      calc (Y.filter (fun W => f W = W')).card
          = Nat.card (Y.filter (fun W => f W = W')) := (Nat.card_eq_finsetCard _).symm
        _ ≤ Nat.card (GHom ρ W₀ W₁) := Nat.card_le_card_of_injective enc henc
        _ ≤ q := GHom.card_le ρ (hY W₀ hW₀).1 hW₁
    have hcard : X.card = Y.card + 1 := (Finset.card_erase_add_one hW₁X).symm
    rw [hcard, Finset.sum_range_succ']
    have hsum : ∑ j ∈ Finset.range (k + 1), q ^ (j + 1) =
        q * ∑ j ∈ Finset.range (k + 1), q ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum, pow_zero]
    have := Nat.mul_le_mul_left q hIH
    omega

end Main


end DerivedHead
end SymmetricSubgroupAsymptotics
