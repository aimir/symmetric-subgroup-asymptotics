import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Field.ZMod
import Lean.Elab.Tactic.Omega

/-! Evaluation separators for actual spaces of binary linear maps.
The line-slice bound is an explicit hypothesis on the original operator
space. A rank-two evaluation removes at least two dimensions. If no such
evaluation remains, a remainder of dimension at least two has one common
image line. No separator or tensor identification is supplied as a premise. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.LinearMapEvaluationSeparator

section General

variable {k V H : Type*} [Field k]
    [AddCommGroup V] [Module k V] [AddCommGroup H] [Module k H]

def evaluation (L : Submodule k (V →ₗ[k] H)) (v : V) : L →ₗ[k] H where
  toFun f := f.1 v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def vanishingAt (L : Submodule k (V →ₗ[k] H)) (v : V) :
    Submodule k (V →ₗ[k] H) where
  carrier := {f | f ∈ L ∧ f v = 0}
  zero_mem' := ⟨L.zero_mem, rfl⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨L.add_mem hf.1 hg.1, by simp [hf.2, hg.2]⟩
  smul_mem' := by
    intro c f hf
    exact ⟨L.smul_mem c hf.1, by simp [hf.2]⟩

theorem vanishingAt_le (L : Submodule k (V →ₗ[k] H)) (v : V) :
    vanishingAt L v ≤ L := fun _ hf => hf.1

def vanishingAtEquivKer (L : Submodule k (V →ₗ[k] H)) (v : V) :
    vanishingAt L v ≃ₗ[k] (evaluation L v).ker where
  toFun f := ⟨⟨f.1, f.2.1⟩, f.2.2⟩
  invFun f := ⟨f.1.1, f.1.2, f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Original maps taking every input into the indicated actual image line. -/
def imageLineSlice (L : Submodule k (V →ₗ[k] H)) (h : H) :
    Submodule k (V →ₗ[k] H) where
  carrier := {f | f ∈ L ∧ ∀ v, f v ∈ Submodule.span k {h}}
  zero_mem' := ⟨L.zero_mem, fun _ => (Submodule.span k {h}).zero_mem⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨L.add_mem hf.1 hg.1, fun v =>
      (Submodule.span k {h}).add_mem (hf.2 v) (hg.2 v)⟩
  smul_mem' := by
    intro c f hf
    exact ⟨L.smul_mem c hf.1, fun v =>
      (Submodule.span k {h}).smul_mem c (hf.2 v)⟩

theorem imageLineSlice_mono {K L : Submodule k (V →ₗ[k] H)} (hKL : K ≤ L)
    (h : H) : imageLineSlice K h ≤ imageLineSlice L h :=
  fun _ hf => ⟨hKL hf.1, hf.2⟩

/-- Vanishing on every vector in W detects only the zero original map. -/
def Separates (L : Submodule k (V →ₗ[k] H)) (W : Submodule k V) : Prop :=
  ∀ f ∈ L, (∀ v ∈ W, f v = 0) → f = 0

theorem separates_span_sup (L : Submodule k (V →ₗ[k] H))
    (v : V) (W : Submodule k V) (hW : Separates (vanishingAt L v) W) :
    Separates L (Submodule.span k {v} ⊔ W) := by
  intro f hf hz
  apply hW f ⟨hf, hz v (Submodule.mem_sup_left (Submodule.mem_span_singleton_self v))⟩
  intro x hx
  exact hz x (Submodule.mem_sup_right hx)

theorem span_singleton_finrank_le_one [FiniteDimensional k V] (v : V) :
    Module.finrank k (Submodule.span k {v}) ≤ 1 := by
  by_cases hv : v = 0
  · rw [hv, Submodule.span_zero_singleton, finrank_bot]
    decide
  · exact (finrank_span_singleton hv).le

variable [FiniteDimensional k V] [FiniteDimensional k H]

theorem evaluation_rank_nullity (L : Submodule k (V →ₗ[k] H)) (v : V) :
    Module.finrank k (evaluation L v).range +
      Module.finrank k (vanishingAt L v) = Module.finrank k L := by
  have h := (evaluation L v).finrank_range_add_finrank_ker
  rwa [← (vanishingAtEquivKer L v).finrank_eq] at h

theorem evaluation_rank_pos (L : Submodule k (V →ₗ[k] H))
    (f : V →ₗ[k] H) (hf : f ∈ L) (v : V) (hfv : f v ≠ 0) :
    1 ≤ Module.finrank k (evaluation L v).range := by
  apply Submodule.one_le_finrank_iff.mpr
  intro hz
  have hm : f v ∈ (evaluation L v).range := ⟨⟨f, hf⟩, rfl⟩
  rw [hz] at hm
  exact hfv hm

/-- A crude separator needs at most one input per original map dimension. -/
theorem exists_separator_subspace_le_finrank (L : Submodule k (V →ₗ[k] H)) :
    ∃ W : Submodule k V, Module.finrank k W ≤ Module.finrank k L ∧ Separates L W := by
  classical
  suffices h : ∀ n (L : Submodule k (V →ₗ[k] H)), Module.finrank k L = n →
      ∃ W : Submodule k V, Module.finrank k W ≤ n ∧ Separates L W from h _ L rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro L hdim
      by_cases hL : L = ⊥
      · refine ⟨⊥, by simp, ?_⟩
        intro f hf _
        simpa only [hL, Submodule.mem_bot] using hf
      obtain ⟨f, hf, hfn⟩ := L.ne_bot_iff.mp hL
      obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
        by_contra hn
        apply hfn
        ext v
        by_contra hv
        exact hn ⟨v, hv⟩
      have hpos := evaluation_rank_pos L f hf v hv
      have hsum := evaluation_rank_nullity L v
      have hlt : Module.finrank k (vanishingAt L v) < n := by omega
      obtain ⟨W, hW, hsep⟩ := ih _ hlt (vanishingAt L v) rfl
      refine ⟨Submodule.span k {v} ⊔ W, ?_, separates_span_sup L v W hsep⟩
      have hadd := Submodule.finrank_add_le_finrank_add_finrank
        (Submodule.span k {v}) W
      have hone := span_singleton_finrank_le_one (k := k) v
      omega

end General

section Binary

variable {V H : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup H] [Module (ZMod 2) H]
    [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) H]

private theorem binary_nonzero_eq_of_rank_le_one
    (S : Submodule (ZMod 2) H) (hS : Module.finrank (ZMod 2) S ≤ 1)
    {a b : H} (ha : a ∈ S) (hb : b ∈ S) (han : a ≠ 0) (hbn : b ≠ 0) : a = b := by
  have hspan : Submodule.span (ZMod 2) {a} ≤ S :=
    Submodule.span_le.mpr (by simpa using ha)
  have heq : Submodule.span (ZMod 2) {a} = S :=
    Submodule.eq_of_le_of_finrank_le hspan (by
      rw [finrank_span_singleton han]
      exact hS)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (heq.symm ▸ hb)
  have hbits : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide +kernel
  rcases hbits c with rfl | rfl
  · exact (hbn (by simpa using hc.symm)).elim
  · simpa using hc

/-- Locally rank-one evaluation has a common image line once the original
operator space has dimension at least two. This is a theorem over F₂,
not an assumed classification of a supplied tensor space. -/
theorem common_image_line_of_evaluation_rank_le_one
    (L : Submodule (ZMod 2) (V →ₗ[ZMod 2] H))
    (hL : 2 ≤ Module.finrank (ZMod 2) L)
    (heval : ∀ v, Module.finrank (ZMod 2) (evaluation L v).range ≤ 1) :
    ∃ h : H, h ≠ 0 ∧ L ≤ imageLineSlice L h := by
  classical
  have hlocal : ∀ f ∈ L, ∀ g ∈ L, ∀ v, f v ≠ 0 → g v ≠ 0 → f v = g v := by
    intro f hf g hg v hfv hgv
    exact binary_nonzero_eq_of_rank_le_one _ (heval v)
      ⟨⟨f, hf⟩, rfl⟩ ⟨⟨g, hg⟩, rfl⟩ hfv hgv
  have hn : L ≠ ⊥ := Submodule.one_le_finrank_iff.mp (by omega)
  obtain ⟨g, hg, hgn⟩ := L.ne_bot_iff.mp hn
  obtain ⟨x, hgx⟩ : ∃ x, g x ≠ 0 := by
    by_contra hx
    apply hgn
    ext x
    by_contra hgx
    exact hx ⟨x, hgx⟩
  have hsum := evaluation_rank_nullity L x
  have hvn : vanishingAt L x ≠ ⊥ :=
    Submodule.one_le_finrank_iff.mp (by have := heval x; omega)
  obtain ⟨f, hf, hfn⟩ := (vanishingAt L x).ne_bot_iff.mp hvn
  have hfx : f x = 0 := hf.2
  let C := Submodule.span (ZMod 2) {g x}
  have hxC : g x ∈ C := Submodule.mem_span_singleton_self (g x)
  have hfC : ∀ y, f y ∈ C := by
    intro y
    by_cases hfy : f y = 0
    · rw [hfy]
      exact C.zero_mem
    by_cases hgy : g y = 0
    · have h := hlocal f hf.1 g hg (x+y)
        (by simpa only [map_add, hfx, zero_add] using hfy)
        (by simpa only [map_add, hgy, add_zero] using hgx)
      have he : f y = g x := by simpa only [map_add, hfx, hgy, zero_add, add_zero] using h
      exact he.symm ▸ hxC
    have hfg : f y = g y := hlocal f hf.1 g hg y hfy hgy
    by_cases hxy : g (x+y) = 0
    · have hz : g x + f y = 0 := by simpa only [map_add, ← hfg] using hxy
      have hm : g x + f y ∈ C := hz.symm ▸ C.zero_mem
      simpa only [add_sub_cancel_left] using C.sub_mem hm hxC
    have he : f y = g x + f y := by
      simpa only [map_add, hfx, zero_add, ← hfg] using
        hlocal f hf.1 g hg (x+y)
          (by simpa only [map_add, hfx, zero_add] using hfy) hxy
    exact (hgx (add_right_cancel (he.symm.trans (zero_add (f y)).symm))).elim
  obtain ⟨y, hfy⟩ : ∃ y, f y ≠ 0 := by
    by_contra hy
    apply hfn
    ext y
    by_contra hfy
    exact hy ⟨y, hfy⟩
  refine ⟨g x, hgx, ?_⟩
  intro a ha
  refine ⟨ha, ?_⟩
  intro z
  change a z ∈ C
  by_contra haz
  have hfnz : f z = 0 := by
    by_contra hfz
    have han : a z ≠ 0 := fun hz => haz (hz.symm ▸ C.zero_mem)
    exact haz ((hlocal f hf.1 a ha z hfz han) ▸ hfC z)
  have hay : a y ∈ C := by
    by_cases hay : a y = 0
    · exact hay.symm ▸ C.zero_mem
    · exact (hlocal f hf.1 a ha y hfy hay) ▸ hfC y
  have han : a (z+y) ≠ 0 := by
    intro hn
    have hm : a z + a y ∈ C := by rw [← map_add, hn]; exact C.zero_mem
    exact haz (by simpa only [add_sub_cancel_right] using C.sub_mem hm hay)
  have he : f y = a z + a y := by
    simpa only [map_add, hfnz, zero_add] using
      hlocal f hf.1 a ha (z+y)
        (by simpa only [map_add, hfnz, zero_add] using hfy) han
  have hm : a z + a y ∈ C := he ▸ hfC y
  exact haz (by simpa only [add_sub_cancel_right] using C.sub_mem hm hay)

/-- A full separating input subspace with the sharp ordinary line-slice
budget. It detects all maps, not only a set of chosen image-line slices. -/
theorem exists_separator_subspace_of_image_line_bound
    (L : Submodule (ZMod 2) (V →ₗ[ZMod 2] H)) (J : ℕ)
    (hJ : ∀ h : H, h ≠ 0 → Module.finrank (ZMod 2) (imageLineSlice L h) ≤ J) :
    ∃ W : Submodule (ZMod 2) V,
      2 * Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) L + max 1 J ∧
      Separates L W := by
  classical
  suffices h : ∀ n (L : Submodule (ZMod 2) (V →ₗ[ZMod 2] H)),
      Module.finrank (ZMod 2) L = n →
      (∀ h : H, h ≠ 0 → Module.finrank (ZMod 2) (imageLineSlice L h) ≤ J) →
      ∃ W : Submodule (ZMod 2) V,
        2 * Module.finrank (ZMod 2) W ≤ n + max 1 J ∧ Separates L W from h _ L rfl hJ
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro L hdim hJ
      by_cases htwo : ∃ v, 2 ≤ Module.finrank (ZMod 2) (evaluation L v).range
      · obtain ⟨v, hv⟩ := htwo
        have hsum := evaluation_rank_nullity L v
        have hlt : Module.finrank (ZMod 2) (vanishingAt L v) < n := by omega
        have hJ' : ∀ h : H, h ≠ 0 →
            Module.finrank (ZMod 2) (imageLineSlice (vanishingAt L v) h) ≤ J := by
          intro h hh
          exact (Submodule.finrank_mono (imageLineSlice_mono (vanishingAt_le L v) h)).trans
            (hJ h hh)
        obtain ⟨W, hW, hsep⟩ := ih _ hlt (vanishingAt L v) rfl hJ'
        refine ⟨Submodule.span (ZMod 2) {v} ⊔ W, ?_, separates_span_sup L v W hsep⟩
        have hadd := Submodule.finrank_add_le_finrank_add_finrank
          (Submodule.span (ZMod 2) {v}) W
        have hone := span_singleton_finrank_le_one (k := ZMod 2) v
        omega
      · have heval : ∀ v, Module.finrank (ZMod 2) (evaluation L v).range ≤ 1 := by
          intro v
          by_contra hv
          exact htwo ⟨v, by omega⟩
        have hsmall : Module.finrank (ZMod 2) L ≤ max 1 J := by
          by_cases hdim1 : Module.finrank (ZMod 2) L ≤ 1
          · exact hdim1.trans (le_max_left _ _)
          obtain ⟨h, hh, hcommon⟩ := common_image_line_of_evaluation_rank_le_one L
            (by omega) heval
          exact ((Submodule.finrank_mono hcommon).trans (hJ h hh)).trans (le_max_right _ _)
        obtain ⟨W, hW, hsep⟩ := exists_separator_subspace_le_finrank L
        exact ⟨W, by omega, hsep⟩

/-- Independent original inputs whose joint evaluation is injective on L.
The empty operator space permits q=0 through the subspace construction. -/
theorem exists_independent_evaluation_separator
    (L : Submodule (ZMod 2) (V →ₗ[ZMod 2] H)) (J : ℕ)
    (hJ : ∀ h : H, h ≠ 0 → Module.finrank (ZMod 2) (imageLineSlice L h) ≤ J) :
    ∃ (q : ℕ) (v : Fin q → V),
      q ≤ (Module.finrank (ZMod 2) L + max 1 J) / 2 ∧
      LinearIndependent (ZMod 2) v ∧
      Function.Injective (fun f : L => fun i => f.1 (v i)) := by
  classical
  obtain ⟨W, hdim, hsep⟩ := exists_separator_subspace_of_image_line_bound L J hJ
  let b := Module.finBasis (ZMod 2) W
  refine ⟨Module.finrank (ZMod 2) W, fun i => (b i : V), ?_,
    b.linearIndependent.map' W.subtype W.ker_subtype, ?_⟩
  · exact (Nat.le_div_iff_mul_le Nat.zero_lt_two).mpr (by omega)
  · intro f g he
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply hsep (f.1-g.1) (L.sub_mem f.2 g.2)
    let d : W →ₗ[ZMod 2] H := (f.1-g.1).comp W.subtype
    have hd : d = 0 := b.ext (fun i => by
      change f.1 (b i : V) - g.1 (b i : V) = 0
      exact sub_eq_zero.mpr (congrFun he i))
    intro x hx
    have hh := LinearMap.congr_fun hd (⟨x, hx⟩ : W)
    simpa only [d, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearMap.sub_apply, LinearMap.zero_apply] using hh

end Binary

end SymmetricSubgroupAsymptotics.LinearMapEvaluationSeparator

end
