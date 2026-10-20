import SymmetricSubgroupAsymptotics.PermutationStabilizerInduced
import SymmetricSubgroupAsymptotics.TraceySolublePermutationFormulaRaw
import SymmetricSubgroupAsymptotics.SolubleOddHall

/-! The soluble permutation formula follows from the stronger retained
soluble-orbit induced-module input. The soluble subgroup is the full actual
acting group; its odd Hall subgroup is constructed by a proved theorem.
An explicit integer cap turns the per-subrepresentation formula into the
single uniform tuple length required by the permutation interface. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics

def traceyBinarySolubleGeneratorCap (s : ℕ) : ℕ :=
  min (ordProj[2] s)
    (s * (traceyBinaryK s).choose (traceyBinaryK s / 2) / 2 ^ traceyBinaryK s)

theorem traceyBinarySolubleGeneratorCap_bounds (s : ℕ) :
    TraceyBinarySolubleFormulaBounds s (traceyBinarySolubleGeneratorCap s) := by
  refine ⟨min_le_left _ _, ?_⟩
  have hle : traceyBinarySolubleGeneratorCap s ≤
      s * (traceyBinaryK s).choose (traceyBinaryK s / 2) / 2 ^ traceyBinaryK s :=
    min_le_right _ _
  have hmul := (Nat.le_div_iff_mul_le
    (by positivity : 0 < 2 ^ traceyBinaryK s)).mp hle
  simpa only [Nat.mul_comm] using hmul

theorem TraceyBinarySolubleFormulaBounds.le_generatorCap {s d : ℕ}
    (h : TraceyBinarySolubleFormulaBounds s d) :
    d ≤ traceyBinarySolubleGeneratorCap s := by
  apply le_min h.1
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ traceyBinaryK s)).2
  simpa only [Nat.mul_comm] using h.2

/-- The stronger orbit theorem, specialized to the actual transitive group
and the trivial local line, supplies the entire raw permutation interface. -/
theorem TraceySolubleOrbitInducedModuleInput.permutationFormulaRaw
    (hTracey : TraceySolubleOrbitInducedModuleInput) :
    TraceySolublePermutationFormulaRawInput := by
  intro G X _ _ _ _ _ _
  by_cases hs0 : Nat.card X = 0
  · refine ⟨0, ?_, ?_⟩
    · rw [hs0]
      simp [TraceyBinarySolubleFormulaBounds, traceyBinaryK]
    · simpa only [hs0] using
        (PermutationStabilizerInduced.uniform_card (k := ZMod 2) (G := G) (X := X))
  · obtain ⟨x⟩ := (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hs0)).1
    let N : Subgroup G := ⊤
    letI : MulAction.IsPretransitive N X := ⟨by
      intro a b
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G a b
      exact ⟨⟨g, Subgroup.mem_top g⟩, hg⟩⟩
    obtain ⟨P, hP⟩ := exists_isTwoComplement_of_isSolvable (G := N)
    let O := MulAction.orbitRel.Quotient N X
    let o₀ : O := Quotient.mk'' x
    letI : Subsingleton O :=
      (MulAction.pretransitive_iff_subsingleton_quotient N X).mp inferInstance
    have horbit : Nat.card o₀.orbit = Nat.card X := by
      change Nat.card (MulAction.orbit N x) = Nat.card X
      rw [MulAction.orbit_eq_univ]
      exact Nat.card_congr (Equiv.Set.univ X)
    let rho := Representation.trivial (ZMod 2) (MulAction.stabilizer G x) (ZMod 2)
    have huniform : UniformSubrepresentationGeneratorBound
        (Representation.ind (MulAction.stabilizer G x).subtype rho)
        (traceyBinarySolubleGeneratorCap (Nat.card X)) := by
      intro M
      obtain ⟨e, he, hgen⟩ := hTracey G X x (ZMod 2) rho N P hP M
      have hformula : TraceyBinarySolubleFormulaBounds (Nat.card X) (e o₀) := by
        simpa only [horbit] using he o₀
      have hcoefficient : min 1 (traceyLocalDualOrbitCount x rho N P) * e o₀ ≤ e o₀ :=
        (Nat.mul_le_mul_right (e o₀) (min_le_left 1 _)).trans_eq (one_mul _)
      apply representationGeneratedBy_mono M.toRepresentation
        (hcoefficient.trans hformula.le_generatorCap)
      rw [Finset.sum_eq_single o₀] at hgen
      · simpa only [Module.finrank_self] using hgen
      · intro b _ hne
        exact (hne (Subsingleton.elim b o₀)).elim
      · simp
    refine ⟨traceyBinarySolubleGeneratorCap (Nat.card X),
      traceyBinarySolubleGeneratorCap_bounds _, ?_⟩
    exact huniform.of_injective (PermutationStabilizerInduced.toInduced x)
      (PermutationStabilizerInduced.toInduced_injective x)

end SymmetricSubgroupAsymptotics
