import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness

/-! Counting the entire subspace lattice of an actual finite binary
vector space. A basis of each subspace is padded by zero to the ambient
dimension, giving a surjection from tuples onto all actual subspaces.
No selected cut family or completeness certificate is required. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- Each actual subspace is the span of an ambient-dimension tuple in
the original vector space, obtained by padding its own basis by zero. -/
theorem binarySubmodule_exists_spanning_tuple (S : Submodule (ZMod 2) V) :
    ∃ f : Fin (Module.finrank (ZMod 2) V) → V,
      Submodule.span (ZMod 2) (Set.range f)=S := by
  classical
  let b := Module.finBasis (ZMod 2) S
  let e : Fin (Module.finrank (ZMod 2) S) →
      Fin (Module.finrank (ZMod 2) V) := Fin.castLE (Submodule.finrank_le S)
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun x : Fin (Module.finrank (ZMod 2) V) => x.val) hij
  let f : Fin (Module.finrank (ZMod 2) V) → S :=
    Function.extend e b (fun _ => 0)
  have hf : Submodule.span (ZMod 2) (Set.range f)=⊤ := by
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨j,rfl⟩
    exact ⟨e j,he.extend_apply _ _ j⟩
  refine ⟨fun i => (f i : V), ?_⟩
  have h := congrArg (Submodule.map S.subtype) hf
  simpa only [Submodule.map_span,← Set.range_comp',Function.comp_def,
    Submodule.map_subtype_top] using h

/-- All subspaces, including zero and the whole space, are counted.
The exponent is the square of the actual ambient binary dimension. -/
theorem binarySubmodule_card_le_square :
    Nat.card (Submodule (ZMod 2) V) ≤
      2^(Module.finrank (ZMod 2) V * Module.finrank (ZMod 2) V) := by
  have hsurj : Function.Surjective
      (fun f : Fin (Module.finrank (ZMod 2) V) → V =>
        Submodule.span (ZMod 2) (Set.range f)) :=
    binarySubmodule_exists_spanning_tuple V
  calc
    Nat.card (Submodule (ZMod 2) V) ≤
        Nat.card (Fin (Module.finrank (ZMod 2) V) → V) :=
      Nat.card_le_card_of_surjective _ hsurj
    _ = 2^(Module.finrank (ZMod 2) V * Module.finrank (ZMod 2) V) := by
      rw [Nat.card_fun,Nat.card_fin,
        Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V),Nat.card_zmod,pow_mul]

/-- A proved upper bound on the actual dimension bounds the entire
cut lattice, without making any admissibility assumption about cuts. -/
theorem binarySubmodule_card_le_of_finrank_le (B : ℕ)
    (hB : Module.finrank (ZMod 2) V≤B) :
    Nat.card (Submodule (ZMod 2) V)≤2^(B*B) :=
  (binarySubmodule_card_le_square V).trans
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul hB hB))

end SymmetricSubgroupAsymptotics
