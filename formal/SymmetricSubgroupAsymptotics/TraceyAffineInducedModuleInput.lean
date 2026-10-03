import SymmetricSubgroupAsymptotics.InducedSubrepresentationCount
import SymmetricSubgroupAsymptotics.FiniteGroupPaddedGenerators
import SymmetricSubgroupAsymptotics.FiniteQuotientInvariantCertificates

/-!
# Published generator inputs used by affine chief layers

This file states only the two results imported from Tracey's 2018 paper and
proves the padding and quotient lemmas needed by the project.  The induced
module statement is Theorem 1.6 together with Corollary 4.27(iii); the
permutation-group statement is Theorem 1.1(1).  Both hypotheses remain
visible at the publication-facing theorem boundary.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

/-- The rounded unconditional bound from Tracey, Corollary 4.27(iii).
Logarithms are base two, as in the numerical parts of the project. -/
noncomputable def traceyInducedGeneratorCeiling (a s : ℕ) : ℕ :=
  ⌈4 * (a : ℝ) * s / Real.sqrt (Real.logb 2 s)⌉₊

/-- Uniform natural exponent paying the finite choices in one actual
elementary affine chief layer when the induced-module generator ceiling is
`H`. -/
def traceyAffineCoefficientExponent
    (a s H g v p : ℕ) : ℕ :=
  a * s * H + H * (v / p) + a * s * (g + 1)

/-- Published induced-module generator theorem in the exact prime-field
specialization used here.  It is deliberately quantified over the local
representation and over every literal subrepresentation of its induction. -/
def TraceyAffineInducedModuleInput : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (G : Type) [Group G] [Finite G]
    (H : Subgroup G), 2 ≤ H.index →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      [FiniteDimensional (ZMod p) V]
      (ρ : Representation (ZMod p) H V)
      (M : Subrepresentation (ρ.ind H.subtype)),
      ∃ n : ℕ,
        n ≤ traceyInducedGeneratorCeiling
          (Module.finrank (ZMod p) V) H.index ∧
        RepresentationGeneratedBy M.toRepresentation n

/-- The unconditional half-dimension specialization of Tracey's induced
module theorem (Theorem 1.6 and Corollary 4.27(iii)).  The floor is expressed
by natural-number division.  Applying the same statement to the dual local
representation supplies the dual bound used by the normal-section argument;
no self-duality assumption is made. -/
def TraceyAffineHalfInducedModuleInput : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (G : Type) [Group G] [Finite G]
    (H : Subgroup G), 2 ≤ H.index →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      [FiniteDimensional (ZMod p) V]
      (ρ : Representation (ZMod p) H V),
      UniformSubrepresentationGeneratorBound (ρ.ind H.subtype)
        (Module.finrank (ZMod p) V * H.index / 2)

/-- Rounded permutation-group generator bound used for quotient actions in
the affine normal and cocycle fibres.  Tracey Theorem 1.1(1) has the smaller
constant `c < 1`, so this ceiling is a direct weakening. -/
noncomputable def traceyPermutationGeneratorCeiling (w : ℕ) : ℕ :=
  ⌈(w : ℝ) / Real.sqrt (Real.logb 2 w)⌉₊

def TraceyPermutationGeneratorInput : Prop :=
  ∀ (w : ℕ) (G : Subgroup (Equiv.Perm (Fin w))), 2 ≤ w →
    MulAction.IsPretransitive G (Fin w) →
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧
      S.card ≤ traceyPermutationGeneratorCeiling w

private def padRepresentationGenerators
    {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) {n H : ℕ}
    (v : Fin n → ρ.asModule) : Fin H → ρ.asModule :=
  fun j ↦ if h : j.1 < n then v ⟨j.1, h⟩ else 0

private theorem range_subset_padRepresentationGenerators
    {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) {n H : ℕ} (hnH : n ≤ H)
    (v : Fin n → ρ.asModule) :
    Set.range v ⊆ Set.range (padRepresentationGenerators ρ (H := H) v) := by
  rintro _ ⟨i, rfl⟩
  let j : Fin H := ⟨i.1, lt_of_lt_of_le i.2 hnH⟩
  refine ⟨j, ?_⟩
  simp [padRepresentationGenerators, j, i.2]

/-- A shorter module-generating tuple can be padded by zero without changing
the generated submodule. -/
theorem representationGeneratedBy_mono
    {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) {n H : ℕ} (hnH : n ≤ H)
    (h : RepresentationGeneratedBy ρ n) :
    RepresentationGeneratedBy ρ H := by
  obtain ⟨v, hv⟩ := h
  refine ⟨padRepresentationGenerators ρ (H := H) v, ?_⟩
  apply top_unique
  rw [← hv]
  exact Submodule.span_mono
    (range_subset_padRepresentationGenerators ρ hnH v)

/-- Tracey's published bound supplies one common padded tuple length for all
subrepresentations of the literal induced module. -/
theorem TraceyAffineInducedModuleInput.uniform
    (hTracey : TraceyAffineInducedModuleInput)
    (p : ℕ) [Fact p.Prime]
    (G : Type) [Group G] [Finite G]
    (H : Subgroup G) (hindex : 2 ≤ H.index)
    (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      [FiniteDimensional (ZMod p) V]
    (ρ : Representation (ZMod p) H V) :
    UniformSubrepresentationGeneratorBound (ρ.ind H.subtype)
      (traceyInducedGeneratorCeiling
        (Module.finrank (ZMod p) V) H.index) := by
  intro M
  obtain ⟨n, hn, hgen⟩ := hTracey p G H hindex V ρ M
  exact representationGeneratedBy_mono M.toRepresentation hn hgen

/-- Tracey's permutation-group theorem, transported back through an
arbitrary faithful action and padded to its uniform rounded length.  The
tuple lives in the original group rather than in an abstract isomorphic
copy of its permutation image. -/
theorem TraceyPermutationGeneratorInput.exists_generating_tuple
    (hTracey : TraceyPermutationGeneratorInput)
    (w : ℕ) (G : Type) [Group G] [Finite G]
    (rho : G →* Equiv.Perm (Fin w)) (hrho : Function.Injective rho)
    (hw : 2 ≤ w)
    (htrans : ∀ x y : Fin w, ∃ g : G, rho g x = y) :
    ∃ g : Fin (traceyPermutationGeneratorCeiling w) → G,
      Subgroup.closure (Set.range g) = ⊤ := by
  let R : Subgroup (Equiv.Perm (Fin w)) := rho.range
  letI : MulAction.IsPretransitive R (Fin w) := ⟨by
    intro x y
    obtain ⟨g, hg⟩ := htrans x y
    exact ⟨⟨rho g, g, rfl⟩, hg⟩⟩
  obtain ⟨S, hS, hScard⟩ := hTracey w R hw inferInstance
  let eS := Fintype.equivFin S
  let f : Fin (traceyPermutationGeneratorCeiling w) → R := fun j ↦
    if h : j.val < Fintype.card S then
      (eS.symm ⟨j.val, h⟩ : S)
    else 1
  have hf : Subgroup.closure (Set.range f) = ⊤ := by
    apply top_unique
    rw [← hS]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    let k := eS ⟨x, hx⟩
    let j : Fin (traceyPermutationGeneratorCeiling w) :=
      ⟨k.val, lt_of_lt_of_le k.isLt (by simpa using hScard)⟩
    apply Subgroup.subset_closure
    refine ⟨j, ?_⟩
    dsimp [f, j]
    rw [if_pos k.isLt]
    exact congrArg (fun z : S ↦ (z : R)) (eS.symm_apply_apply ⟨x, hx⟩)
  let e : G ≃* R := MulEquiv.ofBijective rho.rangeRestrict
    ⟨fun x y h ↦ hrho (congrArg Subtype.val h),
      rho.rangeRestrict_surjective⟩
  refine ⟨fun i ↦ e.symm (f i), ?_⟩
  have hmap : Subgroup.map e.symm.toMonoidHom
      (Subgroup.closure (Set.range f)) =
      Subgroup.map e.symm.toMonoidHom ⊤ :=
    congrArg (Subgroup.map e.symm.toMonoidHom) hf
  simpa only [paddedTupleClosure, MonoidHom.map_closure,
    ← Set.range_comp', Function.comp_def,
    Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective,
    e.symm_apply_apply] using hmap

/-- Every literal quotient of the faithfully acting group is generated by
the images of the same Tracey tuple.  This is the form used simultaneously
for normal-complement graph fibres and for first cohomology. -/
theorem TraceyPermutationGeneratorInput.quotient_exists_generating_tuple
    (hTracey : TraceyPermutationGeneratorInput)
    (w : ℕ) (G : Type) [Group G] [Finite G]
    (rho : G →* Equiv.Perm (Fin w)) (hrho : Function.Injective rho)
    (hw : 2 ≤ w)
    (htrans : ∀ x y : Fin w, ∃ g : G, rho g x = y)
    (N : Subgroup G) [N.Normal] :
    ∃ g : Fin (traceyPermutationGeneratorCeiling w) → G ⧸ N,
      Subgroup.closure (Set.range g) = ⊤ := by
  obtain ⟨g, hg⟩ := hTracey.exists_generating_tuple w G rho hrho hw htrans
  exact ⟨fun i ↦ QuotientGroup.mk' N (g i),
    quotient_generators_full N g hg⟩

end SymmetricSubgroupAsymptotics

end
