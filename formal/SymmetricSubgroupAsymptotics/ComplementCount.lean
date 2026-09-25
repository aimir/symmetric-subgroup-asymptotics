import SymmetricSubgroupAsymptotics.GaussianCount

/-!
# Complements and retained annihilator weights

Complements are counted through actual linear retractions, after choosing one
complement. Annihilator duality then reindexes the quotient-dimension weights
without discarding the subspace that has to be annihilated.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

section Complements

variable {F E : Type*} [Field F] [AddCommGroup E] [Module F E]

/-- A retraction onto `p` is freely specified on a chosen complement. -/
def retractionLinearMapEquiv (p q : Submodule F E) (h : IsCompl p q) :
    {f : E →ₗ[F] p // ∀ x : p, f x = x} ≃ (q →ₗ[F] p) where
  toFun f := f.1.comp q.subtype
  invFun g := ⟨LinearMap.ofIsCompl h LinearMap.id g, by simp⟩
  left_inv f := by
    apply Subtype.ext
    exact LinearMap.ofIsCompl_eq h (fun x ↦ (f.2 x).symm) (fun _ ↦ rfl)
  right_inv g := by ext x; simp

/-- The complements of `p` form a set in bijection with maps from any one
chosen complement to `p`. No preferred zero complement is asserted. -/
def complementLinearMapEquiv (p q : Submodule F E) (h : IsCompl p q) :
    {L : Submodule F E // IsCompl p L} ≃ (q →ₗ[F] p) :=
  p.isComplEquivProj.trans (retractionLinearMapEquiv p q h)

/-- Exact cardinality of the actual complements in a finite vector space. -/
theorem complement_count [Finite F] [FiniteDimensional F E]
    (p : Submodule F E) :
    Nat.card {L : Submodule F E // IsCompl p L} =
      Nat.card F ^ (Module.finrank F (E ⧸ p) * Module.finrank F p) := by
  obtain ⟨q, hq⟩ := p.exists_isCompl
  rw [Nat.card_congr (complementLinearMapEquiv p q hq),
    Module.natCard_eq_pow_finrank (K := F), Module.finrank_linearMap,
    ← (p.quotientEquivOfIsCompl q hq).finrank_eq]

/-- The binary complement factor occurring in every square-admissible lift
fibre. Its exponent retains both quotient and kernel dimensions. -/
theorem binary_complement_count {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (p : Submodule (ZMod 2) E) :
    Nat.card {L : Submodule (ZMod 2) E // IsCompl p L} =
      2 ^ (Module.finrank (ZMod 2) (E ⧸ p) * Module.finrank (ZMod 2) p) := by
  simpa using complement_count p

end Complements

section Annihilators

variable {F E : Type*} [Field F] [AddCommGroup E] [Module F E]
  [FiniteDimensional F E]

/-- Annihilator duality with the required subspace retained on both sides. -/
def retainedAnnihilatorEquiv (Q : Submodule F E) :
    {W : Submodule F E // Q ≤ W} ≃
      {B : Submodule F (Module.Dual F E) // B ≤ Q.dualAnnihilator} where
  toFun W := ⟨W.1.dualAnnihilator,
    Subspace.dualAnnihilator_le_dualAnnihilator_iff.mpr W.2⟩
  invFun B := ⟨B.1.dualCoannihilator, by
    apply Subspace.dualAnnihilator_le_dualAnnihilator_iff.mp
    simpa only [Subspace.dualCoannihilator_dualAnnihilator_eq] using B.2⟩
  left_inv W := Subtype.ext Subspace.dualAnnihilator_dualCoannihilator_eq
  right_inv B := Subtype.ext Subspace.dualCoannihilator_dualAnnihilator_eq

/-- The retained annihilator can equivalently be treated as its own vector
space, with no ambient dual subspaces counted twice. -/
def retainedAnnihilatorSubspaceEquiv (Q : Submodule F E) :
    {W : Submodule F E // Q ≤ W} ≃ Submodule F Q.dualAnnihilator :=
  (retainedAnnihilatorEquiv Q).trans Q.dualAnnihilator.mapIic.toEquiv.symm

theorem retainedAnnihilator_finrank (Q : Submodule F E)
    (W : {W : Submodule F E // Q ≤ W}) :
    Module.finrank F (E ⧸ W.1) =
      Module.finrank F (retainedAnnihilatorSubspaceEquiv Q W) := by
  have hm : (retainedAnnihilatorSubspaceEquiv Q W).map
      Q.dualAnnihilator.subtype = W.1.dualAnnihilator :=
    congrArg Subtype.val (Q.dualAnnihilator.mapIic.apply_symm_apply
      (retainedAnnihilatorEquiv Q W))
  rw [(Subspace.quotEquivAnnihilator W.1).finrank_eq, ← hm]
  exact Submodule.finrank_map_subtype_eq _ _

end Annihilators

section BinaryWeights

open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E]

attribute [local instance] Fintype.ofFinite

private instance : Finite (Module.Dual (ZMod 2) E) :=
  Finite.of_injective (fun f : Module.Dual (ZMod 2) E ↦ (f : E → ZMod 2))
    DFunLike.coe_injective

/-- Annihilator reindexing preserves the full quotient-dimension weight. -/
theorem retainedAnnihilator_weight_sum (Q : Submodule (ZMod 2) E) (k : ℕ) :
    (∑ W : {W : Submodule (ZMod 2) E // Q ≤ W},
      2 ^ (k * Module.finrank (ZMod 2) (E ⧸ W.1))) =
    ∑ B : Submodule (ZMod 2) Q.dualAnnihilator,
      (2 : ℕ) ^ (k * Module.finrank (ZMod 2) B) := by
  classical
  exact Fintype.sum_equiv (retainedAnnihilatorSubspaceEquiv Q) _ _
    (fun W ↦ by rw [retainedAnnihilator_finrank Q W])

/-- The Gaussian coefficient counts subspaces in any finite binary vector
space, independently of the chosen coordinates. -/
theorem binary_rank_count_eq_finrank (j : ℕ) (hj : j ≤ Module.finrank (ZMod 2) E) :
    (Nat.card {B : Submodule (ZMod 2) E // Module.finrank (ZMod 2) B = j} : ℚ) =
      binaryGaussianCoefficient (Module.finrank (ZMod 2) E) j := by
  let e := (Module.finBasis (ZMod 2) E).equivFun
  let eS := Submodule.orderIsoMapComap e
  have hr (B : Submodule (ZMod 2) E) :
      Module.finrank (ZMod 2) B = Module.finrank (ZMod 2) (eS B) :=
    (e.submoduleMap B).finrank_eq
  let eR : {B : Submodule (ZMod 2) E // Module.finrank (ZMod 2) B = j} ≃
      {B : Submodule (ZMod 2) (Fin (Module.finrank (ZMod 2) E) → ZMod 2) //
        Module.finrank (ZMod 2) B = j} :=
    Equiv.subtypeEquiv eS.toEquiv (fun B ↦ by
      change _ ↔ Module.finrank _ (eS B) = j
      rw [← hr B])
  rw [Nat.card_congr eR]
  exact binary_rank_count_eq _ _ hj

/-- Grouping the actual subspaces by dimension produces the explicit
Gaussian polynomial, with every power-of-two weight retained. -/
theorem binary_subspace_weight_sum (k : ℕ) :
    (∑ B : Submodule (ZMod 2) E,
      (2 : ℚ) ^ (k * Module.finrank (ZMod 2) B)) =
    ∑ j ∈ Finset.range (Module.finrank (ZMod 2) E + 1),
      binaryGaussianCoefficient (Module.finrank (ZMod 2) E) j * 2 ^ (k * j) := by
  classical
  let rankIndex (B : Submodule (ZMod 2) E) :
      Fin (Module.finrank (ZMod 2) E + 1) :=
    ⟨Module.finrank (ZMod 2) B, Nat.lt_succ_of_le B.finrank_le⟩
  have hf (j : Fin (Module.finrank (ZMod 2) E + 1)) :
      Nat.card {B : Submodule (ZMod 2) E // rankIndex B = j} =
        Nat.card {B : Submodule (ZMod 2) E // Module.finrank (ZMod 2) B = j.val} := by
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun _ ↦ Fin.ext_iff))
  rw [← Fintype.sum_fiberwise' rankIndex
    (fun j ↦ (2 : ℚ) ^ (k * j.val))]
  calc
    _ = ∑ j : Fin (Module.finrank (ZMod 2) E + 1),
        binaryGaussianCoefficient (Module.finrank (ZMod 2) E) j * 2 ^ (k * j.val) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Nat.card_eq_fintype_card, hf,
        binary_rank_count_eq_finrank j.val (Nat.le_of_lt_succ j.isLt)]
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun j ↦ binaryGaussianCoefficient (Module.finrank (ZMod 2) E) j *
        (2 : ℚ) ^ (k * j)) _

/-- Explicit Gaussian expansion of the retained-annihilator lift weights. -/
theorem retainedAnnihilator_weight_sum_eq_gaussian
    (Q : Submodule (ZMod 2) E) (k : ℕ) :
    (∑ W : {W : Submodule (ZMod 2) E // Q ≤ W},
      (2 : ℚ) ^ (k * Module.finrank (ZMod 2) (E ⧸ W.1))) =
    ∑ j ∈ Finset.range (Module.finrank (ZMod 2) Q.dualAnnihilator + 1),
      binaryGaussianCoefficient (Module.finrank (ZMod 2) Q.dualAnnihilator) j *
        2 ^ (k * j) := by
  calc
    _ = ∑ B : Submodule (ZMod 2) Q.dualAnnihilator,
        (2 : ℚ) ^ (k * Module.finrank (ZMod 2) B) :=
      Fintype.sum_equiv (retainedAnnihilatorSubspaceEquiv Q) _ _
        (fun W ↦ by rw [retainedAnnihilator_finrank Q W])
    _ = _ := binary_subspace_weight_sum k

end BinaryWeights

end SymmetricSubgroupAsymptotics
