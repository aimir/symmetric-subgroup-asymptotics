import SymmetricSubgroupAsymptotics.ComplementCount

/-!
# Counting actual subspace incidences through ordered injections

An arbitrary property of a subspace is retained when its ordered bases are
counted. Consequently any bound on actual ordered linear maps can be divided
by the original general-linear-group factor, without forgetting incidence.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [Finite V]

/-- Ordered independent vectors whose actual span satisfies `P`. -/
abbrev BinaryIncidenceFrames (k : ℕ) (P : Submodule (ZMod 2) V → Prop) :=
  {v : Fin k → V // LinearIndependent (ZMod 2) v ∧
    P (Submodule.span (ZMod 2) (Set.range v))}

private def incidenceFrameSpan {k : ℕ} {P : Submodule (ZMod 2) V → Prop}
    (v : BinaryIncidenceFrames k P) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) (Set.range v.1)

omit [Finite V] in
private theorem incidenceFrameSpan_rank {k : ℕ} {P : Submodule (ZMod 2) V → Prop}
    (v : BinaryIncidenceFrames k P) :
    Module.finrank (ZMod 2) (incidenceFrameSpan v) = k ∧ P (incidenceFrameSpan v) := by
  exact ⟨by simpa [incidenceFrameSpan] using finrank_span_eq_card v.2.1, v.2.2⟩

private theorem incidence_span_inside_eq {k : ℕ}
    (S : Submodule (ZMod 2) V) (hS : Module.finrank (ZMod 2) S = k)
    (v : Fin k → S) (hv : LinearIndependent (ZMod 2) v) :
    Submodule.span (ZMod 2) (Set.range (fun i ↦ (v i : V))) = S := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (v i).2
  · have hli := hv.map' S.subtype (by simp)
    have hrank := finrank_span_eq_card hli
    simpa [Function.comp_def, hS] using hrank

private def incidenceFrameFiberEquiv {k : ℕ} {P : Submodule (ZMod 2) V → Prop}
    (S : Submodule (ZMod 2) V) (hS : Module.finrank (ZMod 2) S = k) (hP : P S) :
    {v : BinaryIncidenceFrames k P // incidenceFrameSpan v = S} ≃
      {v : Fin k → S // LinearIndependent (ZMod 2) v} where
  toFun v := ⟨fun i ↦ ⟨v.1.1 i, by
    exact (le_of_eq v.2) (Submodule.subset_span (Set.mem_range_self i))⟩,
    LinearIndependent.of_comp S.subtype v.1.2.1⟩
  invFun v := ⟨⟨fun i ↦ (v.1 i : V), v.2.map' S.subtype (by simp), by
    rw [incidence_span_inside_eq S hS v.1 v.2]; exact hP⟩,
    incidence_span_inside_eq S hS v.1 v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact ordered-basis count with any subspace property retained. -/
theorem binaryIncidenceFrames_card (k : ℕ) (P : Submodule (ZMod 2) V → Prop) :
    Nat.card (BinaryIncidenceFrames k P) =
      Nat.card {S : Submodule (ZMod 2) V // Module.finrank (ZMod 2) S = k ∧ P S} *
        ∏ i : Fin k, (2 ^ k - 2 ^ (i : ℕ)) := by
  letI := Fintype.ofFinite {S : Submodule (ZMod 2) V //
    Module.finrank (ZMod 2) S = k ∧ P S}
  let e := Equiv.sigmaSubtypeFiberEquiv (incidenceFrameSpan (k := k) (P := P))
    (fun S ↦ Module.finrank (ZMod 2) S = k ∧ P S) incidenceFrameSpan_rank
  have h := Nat.card_congr e
  rw [Nat.card_sigma] at h
  have hc (S : {S : Submodule (ZMod 2) V // Module.finrank (ZMod 2) S = k ∧ P S}) :
      Nat.card {v : BinaryIncidenceFrames k P // incidenceFrameSpan v = S.1} =
        ∏ i : Fin k, (2 ^ k - 2 ^ (i : ℕ)) := by
    rw [Nat.card_congr (incidenceFrameFiberEquiv S.1 S.2.1 S.2.2), card_linearIndependent]
    · simp [S.2.1]
    · omega
  simpa only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card] using h.symm

/-- The frames are equivalent to literal injective linear maps; their range
is the same subspace, so the complete property is preserved. -/
def binaryIncidenceFramesEquivMaps (k : ℕ) (P : Submodule (ZMod 2) V → Prop) :
    BinaryIncidenceFrames k P ≃
      {f : (Fin k → ZMod 2) →ₗ[ZMod 2] V // Function.Injective f ∧ P f.range} where
  toFun v := ⟨(Pi.basisFun (ZMod 2) (Fin k)).constr (ZMod 2) v.1,
    (Pi.basisFun (ZMod 2) (Fin k)).injective_constr_of_linearIndependent v.2.1,
    by simpa only [Module.Basis.constr_range] using v.2.2⟩
  invFun f := ⟨fun i ↦ f.1 (Pi.basisFun (ZMod 2) (Fin k) i),
    (Pi.basisFun (ZMod 2) (Fin k)).linearIndependent.map' f.1
      (LinearMap.ker_eq_bot.mpr f.2.1), by
    have hr := (Pi.basisFun (ZMod 2) (Fin k)).constr_range
      (S := ZMod 2) (f := fun i ↦ f.1 (Pi.basisFun (ZMod 2) (Fin k) i))
    rw [Module.Basis.constr_self] at hr
    exact hr ▸ f.2.2⟩
  left_inv v := by apply Subtype.ext; funext i; exact Module.Basis.constr_basis _ _ _ _
  right_inv f := by apply Subtype.ext; exact Module.Basis.constr_self _ _ _

/-- The exact incidence identity used before any exceptional-lift estimate. -/
theorem binary_subspace_incidence_count_mul (k : ℕ)
    (P : Submodule (ZMod 2) V → Prop) :
    Nat.card {S : Submodule (ZMod 2) V // Module.finrank (ZMod 2) S = k ∧ P S} *
      (∏ i : Fin k, (2 ^ k - 2 ^ (i : ℕ))) =
      Nat.card {f : (Fin k → ZMod 2) →ₗ[ZMod 2] V // Function.Injective f ∧ P f.range} := by
  rw [← binaryIncidenceFrames_card]
  exact Nat.card_congr (binaryIncidenceFramesEquivMaps k P)

end SymmetricSubgroupAsymptotics
