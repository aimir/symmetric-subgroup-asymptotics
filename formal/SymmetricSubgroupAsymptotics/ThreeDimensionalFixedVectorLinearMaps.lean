import SymmetricSubgroupAsymptotics.IndependentSpanComplementCardinality
import Mathlib.Tactic.FinCases

/-! An injective linear map fixing a nonzero vector in dimension three
has two independent free images. The exact successive capacities are
q^3-q and q^3-q^2, without a matrix-group count. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ThreeDimensionalFixedVectorLinearMaps

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [Finite W]

theorem card_le (hd : Module.finrank K W = 3) (w : W) (hw : w ≠ 0) :
    Nat.card {f : W →ₗ[K] W // Function.Injective f ∧ f w = w} ≤
      (Nat.card W - Nat.card K) * (Nat.card W - Nat.card K ^ 2) := by
  letI : FiniteDimensional K W := Module.Finite.of_finite
  have hs : LinearIndepOn K id ({w} : Set W) := LinearIndepOn.singleton hw
  let I := hs.extend (Set.subset_univ _)
  let b : Module.Basis I K W := Module.Basis.extend hs
  let i : I := ⟨w, hs.subset_extend _ (by simp)⟩
  have hi : b i = w := Module.Basis.extend_apply_self hs i
  letI : Fintype I := Fintype.ofFinite I
  have hI : Nat.card I = 3 := by
    have hh := Module.finrank_eq_card_basis b
    simpa only [hd, Nat.card_eq_fintype_card] using hh.symm
  let J := {j : I // j ≠ i}
  letI : Fintype J := Fintype.ofFinite J
  have hJ : Fintype.card J = 2 := by
    have hh : Nat.card J = Nat.card I - 1 := by
      simp only [J, Nat.card_eq_fintype_card]
      simp [Fintype.card_subtype_compl]
    simpa only [hI, Nat.card_eq_fintype_card] using hh
  let t : Fin 2 ≃ J := (Fintype.equivFinOfCardEq hJ).symm
  let j : I := (t 0).val
  let k : I := (t 1).val
  have hji : j ≠ i := (t 0).property
  have hki : k ≠ i := (t 1).property
  have hkj : k ≠ j := by
    intro h
    have hh : t 1 = t 0 := Subtype.ext h
    exact (by decide : (1 : Fin 2) ≠ 0) (t.injective hh)
  have hcover (l : I) : l = i ∨ l = j ∨ l = k := by
    by_cases hl : l = i
    · exact Or.inl hl
    obtain ⟨r, hr⟩ := t.surjective (⟨l, hl⟩ : J)
    fin_cases r
    · exact Or.inr (Or.inl (congrArg Subtype.val hr).symm)
    · exact Or.inr (Or.inr (congrArg Subtype.val hr).symm)
  let E := {f : W →ₗ[K] W // Function.Injective f ∧ f w = w}
  have hLI (f : E) : LinearIndependent K (f.val ∘ b) :=
    b.linearIndependent.map' f.val (LinearMap.ker_eq_bot.mpr f.property.1)
  have hfirst (f : E) : f.val (b j) ∉ Submodule.span K (Set.range ![w]) := by
    have hh := (hLI f).notMem_span_image (s := ({i} : Set I)) hji
    simpa only [Set.image_singleton, Function.comp_apply, hi, f.property.2,
      Matrix.range_cons_empty] using hh
  have hsecond (f : E) : f.val (b k) ∉
      Submodule.span K (Set.range ![w, f.val (b j)]) := by
    have hk' : k ∉ ({i, j} : Set I) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hki, hkj⟩
    have hh := (hLI f).notMem_span_image hk'
    simpa only [Set.image_pair, Function.comp_apply, hi, f.property.2,
      Matrix.range_cons_cons_empty] using hh
  let U := {u : W // u ∉ Submodule.span K (Set.range ![w])}
  let s : U → Fin 2 → W := fun u => ![w, u.val]
  letI : Fintype W := Fintype.ofFinite W
  letI : Fintype U := Fintype.ofFinite U
  letI (u : U) : Fintype {z : W // z ∉ Submodule.span K (Set.range (s u))} :=
    Fintype.ofFinite _
  have hwLI : LinearIndependent K ![w] := by
    simpa only [linearIndependent_unique_iff, Matrix.cons_val_zero] using hw
  have hsLI (u : U) : LinearIndependent K (s u) := by
    have hh := hwLI.finSnoc u.property
    have heq : (Fin.snoc ![w] u.val : Fin 2 → W) = s u := by
      funext r
      fin_cases r <;> rfl
    rw [heq] at hh
    exact hh
  let chart : E → ((u : U) × {z : W // z ∉ Submodule.span K (Set.range (s u))}) :=
    fun f => ⟨⟨f.val (b j), hfirst f⟩, ⟨f.val (b k), hsecond f⟩⟩
  have hchart : Function.Injective chart := by
    intro f g hfg
    have hj : f.val (b j) = g.val (b j) := congrArg
      (fun z : ((u : U) × {z : W // z ∉ Submodule.span K (Set.range (s u))}) =>
        z.1.val) hfg
    have hk : f.val (b k) = g.val (b k) := congrArg
      (fun z : ((u : U) × {z : W // z ∉ Submodule.span K (Set.range (s u))}) =>
        z.2.val) hfg
    apply Subtype.ext
    apply b.ext
    intro l
    rcases hcover l with hl | hl | hl
    · rw [hl, hi, f.property.2, g.property.2]
    · simpa only [hl] using hj
    · simpa only [hl] using hk
  have hU : Nat.card U = Nat.card W - Nat.card K := by
    simpa only [pow_one] using
      IndependentSpanComplementCardinality.card_complement_span ![w] hwLI
  calc
    Nat.card E ≤ Nat.card ((u : U) × {z : W // z ∉ Submodule.span K (Set.range (s u))}) :=
      Nat.card_le_card_of_injective chart hchart
    _ = Nat.card U * (Nat.card W - Nat.card K ^ 2) :=
      IndependentSpanComplementCardinality.card_sigma_complement_span s hsLI
    _ = (Nat.card W - Nat.card K) * (Nat.card W - Nat.card K ^ 2) := by rw [hU]

end SymmetricSubgroupAsymptotics.ThreeDimensionalFixedVectorLinearMaps
