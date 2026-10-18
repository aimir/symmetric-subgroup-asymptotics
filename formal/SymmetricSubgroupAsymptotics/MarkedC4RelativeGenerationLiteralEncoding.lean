import SymmetricSubgroupAsymptotics.MarkedC4PublishedEncodingReduction

/-! A bounded tuple over the same retained literal subgroup is an
injective encoding. Only ordinary generation, source indexing and literal
membership in a target family are inputs; no marked estimate is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.RelativeGenerationLiteral

variable {b l : ℕ} {A : Type} [Fintype A]
  (D : Subgroup (PermutationGroup b))
  (source : A → Subgroup (PermutationGroup b))
  (hsource : Function.Injective source) (hD : ∀ a, source a ≤ D)
  (K : ∀ a, Subgroup (source a)) (tuple : ∀ a, Fin l → source a)
  (hgen : ∀ a, Subgroup.closure (Set.range (tuple a) ∪ K a)=⊤)
  (P : Subgroup (PermutationGroup b) → Prop)
  (hP : ∀ a, P ((K a).map (source a).subtype))

abbrev Target := {J : Subgroup (PermutationGroup b) // P J}
def target : Target P → Subgroup (PermutationGroup b) := Subtype.val

def ambientTuple (a : A) (i : Fin l) : D := ⟨tuple a i,hD a (tuple a i).property⟩
def retained (a : A) : Target P := ⟨(K a).map (source a).subtype,hP a⟩
def code (a : A) : Target P × (Fin l → D) :=
  (retained source K P hP a,ambientTuple D source hD tuple a)

include hgen in
/-- The original subgroup is recovered as the closure of its actual core
and its actual displayed generators in the same ambient permutation group. -/
theorem recovery (a : A) :
    Subgroup.closure (Set.range (fun i => (tuple a i : PermutationGroup b)) ∪
      (K a).map (source a).subtype)=source a := by
  let T := Subgroup.closure (Set.range (fun i => (tuple a i : PermutationGroup b)) ∪
    (K a).map (source a).subtype)
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨i,rfl⟩ := hx
      exact (tuple a i).property
    · obtain ⟨k,_,rfl⟩ := hx
      exact k.property
  · intro x hx
    have hle : Subgroup.closure (Set.range (tuple a) ∪ K a) ≤
        T.comap (source a).subtype := by
      apply (Subgroup.closure_le _).mpr
      intro k hk
      apply Subgroup.subset_closure
      rcases hk with hk | hk
      · obtain ⟨i,rfl⟩ := hk
        exact Or.inl ⟨i,rfl⟩
      · exact Or.inr ⟨k,hk,rfl⟩
    rw [hgen a] at hle
    exact hle (Subgroup.mem_top (⟨x,hx⟩ : source a))

include hsource hgen in
theorem code_injective : Function.Injective (code D source hD K tuple P hP) := by
  intro a a' he
  apply hsource
  have hk : (K a).map (source a).subtype=(K a').map (source a').subtype :=
    congrArg (fun z => z.1.1) he
  have ht : (fun i => (tuple a i : PermutationGroup b))=
      (fun i => (tuple a' i : PermutationGroup b)) := by
    funext i
    exact congrArg (fun z => ((z.2 i : D) : PermutationGroup b)) he
  calc
    source a = Subgroup.closure (Set.range (fun i => (tuple a i : PermutationGroup b)) ∪
        (K a).map (source a).subtype) := (recovery source K tuple hgen a).symm
    _ = Subgroup.closure (Set.range (fun i => (tuple a' i : PermutationGroup b)) ∪
        (K a').map (source a').subtype) := by rw [hk,ht]
    _ = source a' := recovery source K tuple hgen a'

/-- Literal recovery, rather than a count comparison, constructs the code.
The target core is the injective image of precisely the same selected K. -/
def encoding : PermutationRelativeGeneratorEncoding b l A (Target P) D source (target P) where
  K := K
  S a := Finset.univ.image (tuple a)
  generates a := by simpa using hgen a
  generator_card a := (Finset.card_image_le).trans (by simp)
  code := code D source hD K tuple P hP
  core_hom_card a := by
    let e := (K a).equivMapOfInjective (source a).subtype Subtype.coe_injective
    exact (Nat.card_congr (homPrecompEquiv e)).symm
  code_injective := code_injective D source hsource hD K tuple hgen P hP

/-- At this fixed degree, the source/target moment identities are
identities by definition of the two actual finite families. -/
def row (q : ℕ → ℝ)
    (hcost : (Fintype.card D : ℝ)^l ≤ (2 : ℝ)^(q b)) :
    RelativeGeneratorEncodingRow
      (fun _ r => ∑ a : A, (Nat.card (source a →* Multiplicative (ZMod 4)) : ℝ)^r)
      (fun _ r => ∑ z : Target P, (Nat.card (z.1 →* Multiplicative (ZMod 4)) : ℝ)^r)
      q l b where
  A := A
  B := Target P
  X := D
  fintypeA := inferInstance
  fintypeB := inferInstance
  fintypeX := inferInstance
  source := source
  target := target P
  encoding := encoding D source hsource hD K tuple hgen P hP
  source_identity _ := rfl
  target_identity _ := rfl
  alphabet_bound := hcost
end SymmetricSubgroupAsymptotics.MarkedC4.RelativeGenerationLiteral
