import SymmetricSubgroupAsymptotics.MarkedC4ActualLargeOrbitRelativeRow

/-! A container is charged once per original group, not once per relative
generator. The unmarked alphabet is the dependent union of the actual
container tuple spaces. This keeps the partition/container cost additive
in the exponent when applying the large-orbit reduction. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ContainerRelativeEncoding

variable {b l : ℕ} {A I : Type} [Fintype A] [Fintype I]
  (D : I → Subgroup (PermutationGroup b))
  (source : A → Subgroup (PermutationGroup b))
  (hsource : Function.Injective source)
  (container : A → I) (hD : ∀ a, source a ≤ D (container a))
  (K : ∀ a, Subgroup (source a)) (tuple : ∀ a, Fin l → source a)
  (hgen : ∀ a, Subgroup.closure (Set.range (tuple a) ∪ K a) = ⊤)
  (P : Subgroup (PermutationGroup b) → Prop)
  (hP : ∀ a, P ((K a).map (source a).subtype))

abbrev Words := Σ i : I, Fin l → D i
abbrev Target := {J : Subgroup (PermutationGroup b) // P J}

def code (a : A) : Target P × Words (l := l) D :=
  (⟨(K a).map (source a).subtype, hP a⟩,
    ⟨container a, fun j => ⟨tuple a j, hD a (tuple a j).property⟩⟩)

include hsource hgen in
omit [Fintype I] in
theorem code_injective :
    Function.Injective (code D source container hD K tuple P hP) := by
  intro a a' he
  apply hsource
  have hk : (K a).map (source a).subtype = (K a').map (source a').subtype :=
    congrArg (fun z : Target P × Words (l := l) D => z.1.val) he
  have ht : (fun j => (tuple a j : PermutationGroup b)) =
      (fun j => (tuple a' j : PermutationGroup b)) := by
    funext j
    exact congrArg (fun z : Target P × Words (l := l) D =>
      (z.2.2 j : PermutationGroup b)) he
  calc
    source a = Subgroup.closure
        (Set.range (fun j => (tuple a j : PermutationGroup b)) ∪
          (K a).map (source a).subtype) :=
      (RelativeGenerationLiteral.recovery source K tuple hgen a).symm
    _ = Subgroup.closure
        (Set.range (fun j => (tuple a' j : PermutationGroup b)) ∪
          (K a').map (source a').subtype) := by rw [hk, ht]
    _ = source a' := RelativeGenerationLiteral.recovery source K tuple hgen a'

theorem words_card : Fintype.card (Words (l := l) D) =
    ∑ i : I, (Fintype.card (D i))^l := by
  simp only [Words, Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin]

include hsource hgen container hD hP in
/-- The exact complete marked sum keeps one global container choice.
Only actual subgroup recovery and restriction of characters enter. -/
theorem moment_le (r : ℕ) :
    (∑ a : A, (Nat.card (source a →* Multiplicative (ZMod 4)) : ℝ)^r) ≤
      (∑ i : I, (Fintype.card (D i) : ℝ)^l) * (2 : ℝ)^(2*r*l) *
        ∑ z : Target P, (Nat.card (z.1 →* Multiplicative (ZMod 4)) : ℝ)^r := by
  let c := code D source container hD K tuple P hP
  have hc := code_injective D source hsource container hD K tuple hgen P hP
  have hf : ∀ z, Nat.card {a : A // c a = z} ≤ 1 := by
    intro z
    rw [Finite.card_le_one_iff_subsingleton]
    exact ⟨fun x y => Subtype.ext (hc (x.property.trans y.property.symm))⟩
  have hs := homMoment_sum_le_of_relativeGenerator_encoding
    (fun a => source a) K (fun a => Finset.univ.image (tuple a)) c
    (fun z : Target P × Words (l := l) D =>
      (Nat.card (z.1.1 →* Multiplicative (ZMod 4)) : ℝ)^r)
    1 l r (fun a => by simpa using hgen a)
    (fun a => (Finset.card_image_le).trans (by simp)) (fun _ => by positivity)
    (fun a => by
      let e := (K a).equivMapOfInjective (source a).subtype Subtype.coe_injective
      have he := (Nat.card_congr
        (homPrecompEquiv (A := Multiplicative (ZMod 4)) e)).symm
      exact le_of_eq (congrArg (fun n : ℕ => (n : ℝ)^r) he)) hf
  have hw : (Fintype.card (Words (l := l) D) : ℝ) =
      ∑ i : I, (Fintype.card (D i) : ℝ)^l := by
    rw [words_card]
    simp
  have hp : (∑ z : Target P × Words (l := l) D,
      (Nat.card (z.1.1 →* Multiplicative (ZMod 4)) : ℝ)^r) =
      (Fintype.card (Words (l := l) D) : ℝ) *
        ∑ z : Target P, (Nat.card (z.1 →* Multiplicative (ZMod 4)) : ℝ)^r := by
    rw [Fintype.sum_prod_type]
    change (∑ z : Target P, ∑ _w : Words (l := l) D,
      (Nat.card (z.1 →* Multiplicative (ZMod 4)) : ℝ)^r) = _
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
  simp only [Nat.cast_one, one_mul] at hs
  rw [hp, hw] at hs
  exact hs.trans_eq (by ring)

end SymmetricSubgroupAsymptotics.MarkedC4.ContainerRelativeEncoding
end
