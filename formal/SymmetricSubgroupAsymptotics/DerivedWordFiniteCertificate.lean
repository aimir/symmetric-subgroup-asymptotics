import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.FiniteGeneratorNormality
import SymmetricSubgroupAsymptotics.FiniteGroupCertificates
import SymmetricSubgroupAsymptotics.FiniteQuotientInvariantCertificates

/-! Small derived-group certificates on the original generator closure.
Only the derived subgroup is enumerated. Its generators are actual derived
words, its rows have checked Cayley transitions and words, and original
generator conjugates and commutators are located among those same rows.
These obligations prove normality, equality with the actual derived group,
and its exact cardinality without an ambient group enumeration. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

variable {G ι κ : Type*} [Group G]

/-- The derived words are evaluated inside the closure of the same
original tuple, so membership is in that group's derived subgroup. -/
def derivedWordGenerators (g : ι → G) (words : κ → DerivedGeneratorWord ι) :
    κ → Subgroup.closure (Set.range g) :=
  fun j => (words j).eval (closureGenerators g)

def derivedWordClosure (g : ι → G) (words : κ → DerivedGeneratorWord ι) :
    Subgroup (Subgroup.closure (Set.range g)) :=
  Subgroup.closure (Set.range (derivedWordGenerators g words))

theorem derivedWordClosure_le_commutator
    (g : ι → G) (words : κ → DerivedGeneratorWord ι) :
    derivedWordClosure g words ≤ commutator (Subgroup.closure (Set.range g)) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (words j).eval_mem_commutator (closureGenerators g)

/-- Every finite equation concerns the original generated group.
Forward conjugates suffice because this group is finite at consumption.
The Cayley certificate separately supplies row words and transitions;
injectivity prevents a cardinality claim based on repeated rows. -/
structure DerivedWordFiniteCertificate
    (g : ι → G) (words : κ → DerivedGeneratorWord ι) (n : ℕ) where
  cayley : FiniteCayleyCertificate (derivedWordGenerators g words) n
  rows_injective : Function.Injective cayley.elements
  conjugateRow : ι → κ → Fin n
  conjugate_eq : ∀ i j, cayley.elements (conjugateRow i j) =
    closureGenerators g i * derivedWordGenerators g words j * (closureGenerators g i)⁻¹
  commutatorRow : ι → ι → Fin n
  commutator_eq : ∀ i j, cayley.elements (commutatorRow i j) =
    ⁅closureGenerators g i, closureGenerators g j⁆

namespace DerivedWordFiniteCertificate

variable [Finite G] {g : ι → G} {words : κ → DerivedGeneratorWord ι} {n : ℕ}
    (C : DerivedWordFiniteCertificate g words n)

include C

/-- The actual original group normalizes the displayed derived-word
closure; no normality of a table or an unrelated abstract group is used. -/
theorem normal : (derivedWordClosure g words).Normal := by
  have h := generated_le_normalizer_of_generator_conjugates
    (derivedWordGenerators g words) (closureGenerators g) (fun i j =>
      (C.cayley.mem_closure_iff _).mpr ⟨C.conjugateRow i j, C.conjugate_eq i j⟩)
  rw [closureGenerators_full g] at h
  exact Subgroup.normalizer_eq_top_iff.mp (top_unique h)

/-- Containing the original generator commutators gives one inclusion;
the derived-word syntax gives the reverse inclusion in the same group. -/
theorem subgroup_eq_commutator :
    derivedWordClosure g words = commutator (Subgroup.closure (Set.range g)) := by
  letI : (derivedWordClosure g words).Normal := C.normal
  apply le_antisymm (derivedWordClosure_le_commutator g words)
  apply commutator_le_of_generator_commutators (derivedWordClosure g words)
    (closureGenerators g) (closureGenerators_full g)
  intro i j
  exact (C.cayley.mem_closure_iff _).mpr
    ⟨C.commutatorRow i j, C.commutator_eq i j⟩

/-- Exact cardinality follows from the injective small Cayley rows,
after identifying their literal closure with the original derived group. -/
theorem card_commutator :
    Nat.card (commutator (Subgroup.closure (Set.range g))) = n := by
  have h := C.cayley.card_closure C.rows_injective
  change Nat.card (derivedWordClosure g words) = n at h
  rwa [C.subgroup_eq_commutator] at h

end DerivedWordFiniteCertificate
end SymmetricSubgroupAsymptotics
