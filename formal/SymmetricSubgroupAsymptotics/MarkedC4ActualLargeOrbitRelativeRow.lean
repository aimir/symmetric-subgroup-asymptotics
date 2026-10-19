import SymmetricSubgroupAsymptotics.MarkedC4ActualLargeOrbitImage
import SymmetricSubgroupAsymptotics.RelativeProjectionGeneratorLifts

/-! The literal large-orbit projection constructs a relative encoding in
each actual permutation container. Its sole group-generation input counts
ordinary generators of that projection's actual image. Container counting
and the asymptotic ordinary generator estimate remain separate. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualLargeOrbitRelative

open ActualLargeOrbitKernel
variable {b l : ℕ} (D : Subgroup (PermutationGroup b)) (C : ℕ)

abbrev Source := {G : Subgroup (PermutationGroup b) // IsSolvable G ∧ G ≤ D}

def sourceCount (r : ℕ) : ℝ :=
  ∑ G : Source D, (Nat.card (G.1 →* Multiplicative (ZMod 4)) : ℝ)^r

/-- Pad an ordinary generating set of the actual projection image, then
lift the tuple to the original source. No abstract replacement is used. -/
theorem exists_relative_tuple (G : Subgroup (PermutationGroup b))
    (hordinary : ∃ S : Finset (projection G C).range, S.card ≤ l ∧
      Subgroup.closure (S : Set (projection G C).range) = ⊤) :
    ∃ t : Fin l → G,
      Subgroup.closure (Set.range t ∪ (projection G C).ker) = ⊤ := by
  obtain ⟨S, hcard, hgen⟩ := hordinary
  obtain ⟨a, ha⟩ := NilpotentGenerationRelative.exists_padded_generating_tuple
    (⊥ : Subgroup (projection G C).range) S hcard (by simpa using hgen)
  have ha' : Subgroup.closure (Set.range a) = ⊤ := by simpa using ha
  obtain ⟨t, _, ht⟩ := RelativeProjectionGeneratorLifts.exists_lifts
    (projection G C) a ha'
  exact ⟨t, ht⟩

/-- The source is recovered from its actual bounded-orbit kernel and its
lifted image generators, all in the same container D. -/
def row (hC : 2 ≤ C)
    (hordinary : ∀ G : Source D,
      ∃ S : Finset (projection G.1 C).range, S.card ≤ l ∧
        Subgroup.closure (S : Set (projection G.1 C).range) = ⊤)
    (q : ℕ → ℝ) (hcost : (Fintype.card D : ℝ)^l ≤ (2 : ℝ)^(q b)) :
    RelativeGeneratorEncodingRow
      (fun _ r => sourceCount D r) (OrbitCutoffFamilies.solubleCount C) q l b := by
  choose tuple htuple using fun G : Source D =>
    exists_relative_tuple C G.1 (hordinary G)
  let K : ∀ G : Source D, Subgroup G.1 := fun G => (projection G.1 C).ker
  have htarget (G : Source D) :
      IsSolvable ((K G).map G.1.subtype) ∧
        OrbitCutoffFamilies.OrbitCutoff C ((K G).map G.1.subtype) := by
    letI : IsSolvable G.1 := G.2.1
    exact (solubleTarget G.1 C hC).property
  let R := RelativeGenerationLiteral.row D
    (fun G : Source D => G.1) Subtype.val_injective (fun G => G.2.2)
    K tuple htuple
    (fun J => IsSolvable J ∧ OrbitCutoffFamilies.OrbitCutoff C J) htarget q hcost
  exact {
    A := R.A
    B := R.B
    X := R.X
    fintypeA := R.fintypeA
    fintypeB := R.fintypeB
    fintypeX := R.fintypeX
    source := R.source
    target := R.target
    encoding := R.encoding
    source_identity := fun _ => rfl
    target_identity := by
      intro r
      have hI : R.fintypeB =
          (inferInstance : Fintype (OrbitCutoffFamilies.SolubleFamily C b)) :=
        Subsingleton.elim _ _
      change OrbitCutoffFamilies.solubleCount C b r =
        (@Finset.univ (OrbitCutoffFamilies.SolubleFamily C b) R.fintypeB).sum
          (fun z => (Nat.card (z.1 →* Multiplicative (ZMod 4)) : ℝ)^r)
      rw [hI]
      rfl
    alphabet_bound := R.alphabet_bound }

end SymmetricSubgroupAsymptotics.MarkedC4.ActualLargeOrbitRelative
end
