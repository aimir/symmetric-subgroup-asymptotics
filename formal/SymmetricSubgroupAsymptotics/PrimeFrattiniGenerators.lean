import SymmetricSubgroupAsymptotics.PrimeFrattini
import SymmetricSubgroupAsymptotics.PrimeCharacterSubgroupCapacity
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Data.Nat.Log
import Mathlib.Logic.Function.Basic

/-! Actual generators obtained by lifting the original prime quotient.
For any onto map, a small subset of the SAME original generator indices
already maps onto the target. No generating-set rank theorem is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
variable {G : Type*} [Group G] [Finite G] {ι : Type*}

/-- Actual generators span the actual prime quotient under evaluation. -/
theorem primeEvaluation_span_eq_top_of_generates (g : ι → G)
    (hg : Subgroup.closure (Set.range g)=⊤) :
    Submodule.span (ZMod p) (Set.range (fun i =>
      primeAbelianizationMap p G (Additive.ofMul (g i))))=⊤ := by
  let S : Submodule (ZMod p) (PrimeAbelianization p G) :=
    Submodule.span (ZMod p) (Set.range (fun i =>
      primeAbelianizationMap p G (Additive.ofMul (g i))))
  let T : Subgroup G := S.toAddSubgroup.toSubgroup.comap (primeAbelianizationGroupMap p G)
  have hclosure : Subgroup.closure (Set.range g) ≤ T := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact Submodule.subset_span ⟨i,rfl⟩
  have hfull : (⊤ : Subgroup G) ≤ T := by simpa only [hg] using hclosure
  apply top_unique
  intro v _
  obtain ⟨x,hx⟩ := primeAbelianizationMap_surjective p G v
  have hmem : primeAbelianizationMap p G x ∈ S :=
    hfull (show x.toMul ∈ (⊤ : Subgroup G) from trivial)
  exact hx ▸ hmem

/-- A spanning family in the prime quotient generates the original finite
p-group. The sole lifting input is the checked exact Frattini kernel. -/
theorem prime_generates_of_evaluation_span (hG : IsPGroup p G) (g : ι → G)
    (hspan : Submodule.span (ZMod p) (Set.range (fun i =>
      primeAbelianizationMap p G (Additive.ofMul (g i))))=⊤) :
    Subgroup.closure (Set.range g)=⊤ := by
  let H := Subgroup.closure (Set.range g)
  let π := primeAbelianizationGroupMap p G
  let W : Submodule (ZMod p) (PrimeAbelianization p G) :=
    AddSubgroup.toZModSubmodule p (Subgroup.toAddSubgroup' (H.map π))
  have hspan_le : Submodule.span (ZMod p) (Set.range (fun i =>
      primeAbelianizationMap p G (Additive.ofMul (g i)))) ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨g i,Subgroup.subset_closure ⟨i,rfl⟩,rfl⟩
  have hW : (⊤ : Submodule (ZMod p) (PrimeAbelianization p G)) ≤ W := by
    simpa only [hspan] using hspan_le
  have hmap : H.map π=⊤ := by
    apply top_unique
    intro v _
    exact hW (show v.toAdd ∈ (⊤ : Submodule (ZMod p) (PrimeAbelianization p G)) from trivial)
  apply frattini_nongenerating
  have h := congrArg (Subgroup.comap π) hmap
  have hker : H ⊔ π.ker=⊤ := by
    simpa only [Subgroup.comap_map_eq,Subgroup.comap_top] using h
  change H ⊔ frattini G=⊤
  rw [← primeAbelianizationGroupMap_ker p G hG]
  exact hker

/-- A generating tuple of length exactly the original scalar-character rank. -/
theorem exists_primeFrattini_generating_tuple (hG : IsPGroup p G) :
    ∃ g : Fin (Module.finrank (ZMod p) (PrimeCharacters p G)) → G,
      Subgroup.closure (Set.range g)=⊤ := by
  let b : Module.Basis (Fin (Module.finrank (ZMod p) (PrimeCharacters p G)))
      (ZMod p) (PrimeAbelianization p G) :=
    Module.finBasisOfFinrankEq (ZMod p) (PrimeAbelianization p G)
      Subspace.dual_finrank_eq
  choose g hg using fun i => primeAbelianizationMap_surjective p G (b i)
  refine ⟨fun i => (g i).toMul,prime_generates_of_evaluation_span p hG _ ?_⟩
  have he : (fun i => primeAbelianizationMap p G (Additive.ofMul (g i).toMul))=b :=
    funext hg
  rw [he]
  exact b.span_eq

/-- For any onto map, select indices from the original generating family.
The selected images generate the SAME target and use at most its prime rank. -/
theorem exists_generating_subtuple_le_primeRank
    {Q : Type*} [Group Q] [Finite Q] (hG : IsPGroup p G)
    (g : ι → G) (hg : Subgroup.closure (Set.range g)=⊤)
    (β : G →* Q) (hβ : Function.Surjective β) :
    ∃ S : Finset ι, S.card ≤ Module.finrank (ZMod p) (PrimeCharacters p Q) ∧
      Subgroup.closure (β '' (g '' (S : Set ι)))=⊤ := by
  classical
  have hgQ : Subgroup.closure (Set.range (fun i => β (g i)))=⊤ := by
    have h := congrArg (Subgroup.map β) hg
    simpa only [MonoidHom.map_closure,← Set.range_comp',
      Subgroup.map_top_of_surjective β hβ,Function.comp_def] using h
  let v : ι → PrimeAbelianization p Q := fun i =>
    primeAbelianizationMap p Q (Additive.ofMul (β (g i)))
  let s : Set (PrimeAbelianization p Q) := Set.range v
  have hs : Submodule.span (ZMod p) s=⊤ :=
    primeEvaluation_span_eq_top_of_generates p (fun i => β (g i)) hgQ
  obtain ⟨t,htsub,htcard,htspan,_⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn (ZMod p) s
  let idx : t → ι := fun x => Classical.choose (htsub x.2)
  have hidx (x : t) : v (idx x)=x := Classical.choose_spec (htsub x.2)
  let S : Finset ι := Finset.univ.image idx
  have hcard : S.card ≤ Module.finrank (ZMod p) (PrimeCharacters p Q) := by
    calc
      S.card ≤ (Finset.univ : Finset t).card := Finset.card_image_le
      _ = t.card := by simp
      _ = _ := htcard.trans (calc
        Module.finrank (ZMod p) (Submodule.span (ZMod p) s) =
            Module.finrank (ZMod p)
              (⊤ : Submodule (ZMod p) (PrimeAbelianization p Q)) :=
          congrArg (fun W : Submodule (ZMod p) (PrimeAbelianization p Q) =>
            Module.finrank (ZMod p) W) hs
        _ = Module.finrank (ZMod p) (PrimeCharacters p Q) := by
          rw [finrank_top,Subspace.dual_finrank_eq])
  have hselected : Submodule.span (ZMod p) (Set.range (fun i : S => v i))=⊤ := by
    apply top_unique
    rw [← hs,← htspan]
    apply Submodule.span_mono
    intro x hx
    let a : t := ⟨x,hx⟩
    have hi : idx a ∈ S := Finset.mem_image.mpr ⟨a,Finset.mem_univ a,rfl⟩
    exact ⟨⟨idx a,hi⟩,hidx a⟩
  have hgenerate : Subgroup.closure (Set.range (fun i : S => β (g i)))=⊤ :=
    prime_generates_of_evaluation_span p (hG.of_surjective β hβ)
      (fun i : S => β (g i)) hselected
  have hrange : Set.range (fun i : S => β (g i))=β '' (g '' (S : Set ι)) := by
    ext q
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨g i,⟨i,i.2,rfl⟩,rfl⟩
    · rintro ⟨x,⟨i,hi,rfl⟩,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩
  exact ⟨S,hcard,hrange ▸ hgenerate⟩

/-- The small subtuple bound follows from the actual target evaluation
quotient order; it is not supplied as a generator-rank hypothesis. -/
theorem exists_generating_subtuple_le_log_card
    {Q : Type*} [Group Q] [Finite Q] (hG : IsPGroup p G)
    (g : ι → G) (hg : Subgroup.closure (Set.range g)=⊤)
    (β : G →* Q) (hβ : Function.Surjective β) :
    ∃ S : Finset ι, S.card ≤ Nat.log p (Nat.card Q) ∧
      Subgroup.closure (β '' (g '' (S : Set ι)))=⊤ := by
  obtain ⟨S,hS,hgen⟩ := exists_generating_subtuple_le_primeRank p hG g hg β hβ
  exact ⟨S,hS.trans (Nat.le_log_of_pow_le (Fact.out : p.Prime).one_lt
    (primeCharacters_pow_finrank_le_card p Q)),hgen⟩

/-- A fixed-length optional-index code pads the selected original subtuple
by identities. It introduces no new generators or changed target map. -/
theorem exists_padded_generating_subtuple
    {Q : Type*} [Group Q] [Finite Q] (hG : IsPGroup p G)
    (g : ι → G) (hg : Subgroup.closure (Set.range g)=⊤)
    (β : G →* Q) (hβ : Function.Surjective β) :
    ∃ t : Fin (Nat.log p (Nat.card Q)) → Option ι,
      Subgroup.closure (Set.range (fun a => β ((t a).elim 1 g)))=⊤ := by
  classical
  obtain ⟨S,hS,hgen⟩ := exists_generating_subtuple_le_log_card p hG g hg β hβ
  let e : S → Fin (Nat.log p (Nat.card Q)) := fun a =>
    ⟨(S.equivFin a).val,Nat.lt_of_lt_of_le (S.equivFin a).isLt hS⟩
  have he : Function.Injective e := by
    intro a b hab
    apply S.equivFin.injective
    apply Fin.ext
    exact congrArg (fun z : Fin (Nat.log p (Nat.card Q)) => z.val) hab
  let t : Fin (Nat.log p (Nat.card Q)) → Option ι :=
    Function.extend e (fun a : S => some (a : ι)) (fun _ => none)
  refine ⟨t,top_unique ?_⟩
  rw [← hgen]
  apply Subgroup.closure_mono
  rintro _ ⟨x,⟨i,hi,rfl⟩,rfl⟩
  let a : S := ⟨i,hi⟩
  refine ⟨e a,?_⟩
  have ht : t (e a)=some i := he.extend_apply _ _ a
  change β ((t (e a)).elim 1 g)=β (g i)
  rw [ht]
  rfl

end SymmetricSubgroupAsymptotics
