import SymmetricSubgroupAsymptotics.CFSGTwistedDSingularTailDimension
import SymmetricSubgroupAsymptotics.CFSGTwistedDSingularNegativeHalf

/-! An actual fixed-space singular submodule has dimension at most
r-1 in natural rank r. The final fixed plane is an anisotropic norm
plane, and literal relative words normalize the first singular axis
before each exact fixed-tail dimension drop. This includes q=2. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDSingularDimensionBound
open CFSGOrthogonalDSerreMatrices CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDHighestPairOperator CFSGTwistedA2FixedField
open CFSGTwistedDSingularTailDimension CFSGTwistedDFixedTailLinear
open CFSGOrthogonalDGenerationForkTorus CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexPrefixPerpendicular

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

private theorem zero_ne_last (n : ℕ) : (0 : Fin (n + 2)) ≠ last n := by
  intro h
  have hv := congrArg Fin.val h
  change 0 = n + 1 at hv
  omega

def firstAxis (n : ℕ) (q : CFSG.PrimePower) : fixedSpace n q :=
  positiveBasis n q 0 (zero_ne_last n)

theorem firstAxis_nonzero (n : ℕ) (q : CFSG.PrimePower) : firstAxis n q ≠ 0 := by
  intro h
  have he := congrArg (fun v : fixedSpace n q => v.val (Sum.inl 0)) h
  change (Pi.single (Sum.inl (0 : Fin (n + 2))) (1 : q.Extension 2) :
    Index (n + 2) → q.Extension 2) (Sum.inl 0) = 0 at he
  rw [Pi.single_eq_same] at he
  exact one_ne_zero he

theorem exists_normalize_subspace (n : ℕ) (q : CFSG.PrimePower)
    (P : Submodule (fixedField q) (fixedSpace n q))
    (hs : ∀ x ∈ P, fixedQuadraticForm n q x = 0) (hP : P ≠ ⊥) :
    ∃ g : relativeRootGroup n q,
      firstAxis n q ∈ P.map (fixedLinearHom n q g).toLinearMap ∧
      ∀ x ∈ P.map (fixedLinearHom n q g).toLinearMap, fixedQuadraticForm n q x = 0 := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  have hvQ := congrArg (fun a : fixedField q => (a : q.Extension 2)) (hs v hv)
  dsimp only at hvQ
  rw [fixedQuadraticForm_apply] at hvQ
  obtain ⟨g, hg⟩ := CFSGTwistedDAllRankSingularOrbit.exists_normalize_all n q v.val v.property hvQ
    (fun he => hv0 (Subtype.ext he))
  refine ⟨g, ⟨v, hv, ?_⟩, ?_⟩
  · apply Subtype.ext
    change (fixedLinearHom n q g v).val = (firstAxis n q).val
    rw [fixedLinearHom_apply]
    exact hg
  · rintro x ⟨y, hy, rfl⟩
    exact (fixedLinearHom_preserves_Q n q g y).trans (hs y hy)

theorem base_singular_axis_bound (q : CFSG.PrimePower)
    (P : Submodule (fixedField q) (fixedSpace 0 q))
    (hs : ∀ x ∈ P, fixedQuadraticForm 0 q x = 0) (hu : firstAxis 0 q ∈ P) :
    P ≤ Submodule.span (fixedField q) {firstAxis 0 q} := by
  intro v hv
  have hp : (fixedQuadraticForm 0 q).polarBilin (firstAxis 0 q) v = 0 := by
    change fixedQuadraticForm 0 q (firstAxis 0 q + v) -
      fixedQuadraticForm 0 q (firstAxis 0 q) - fixedQuadraticForm 0 q v = 0
    rw [hs _ (P.add_mem hu hv), hs _ hu, hs _ hv]
    ring
  have hn := congrArg (fun a : fixedField q => (a : q.Extension 2)) hp
  dsimp only at hn
  rw [fixedQuadraticForm_polar, splitQuadraticForm_polar] at hn
  change CFSGOrthogonalDIndexPolarForm.polar (q.Extension 2)
    (Pi.single (Sum.inl (0 : Fin 2)) 1) v.val = 0 at hn
  rw [polar_positive_basis] at hn
  have hQ := congrArg (fun a : fixedField q => (a : q.Extension 2)) (hs v hv)
  dsimp only at hQ
  rw [fixedQuadraticForm_apply] at hQ
  have hneg (i : Fin 1) : v.val (Sum.inr i.castSucc) = 0 := by
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact hn
  obtain ⟨hlast, hhalf⟩ := CFSGTwistedDSingularNegativeHalf.vanishing_negative_half
    (q.Extension 2) 0 (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2)
    v.val v.property hQ hneg
  have ht : tailRestriction (q.Extension 2) 1 v.val = 0 := by
    funext i
    cases i with
    | inl i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      change v.val (Sum.inl (last 0)) = 0
      exact hlast
    | inr i => exact congrFun hhalf i.succ
  have he := vector_eq_first_of_tail_zero (q.Extension 2) 1 v.val ht hn
  let c : fixedField q := ⟨v.val (Sum.inl 0),
    CFSGTwistedDFixedVectorCoordinates.positive_fixed _ _ _ v.val v.property 0 (zero_ne_last 0)⟩
  have heF : v = c • firstAxis 0 q := Subtype.ext he
  exact Submodule.mem_span_singleton.mpr ⟨c, heF.symm⟩

theorem singular_finrank_le (q : CFSG.PrimePower) :
    ∀ (n : ℕ) (P : Submodule (fixedField q) (fixedSpace n q)),
      (∀ x ∈ P, fixedQuadraticForm n q x = 0) → Module.finrank (fixedField q) P ≤ n + 1 := by
  intro n
  induction n with
  | zero =>
    intro P hs
    by_cases hb : P = ⊥
    · subst P
      exact (finrank_bot (fixedField q) (fixedSpace 0 q)).le.trans (Nat.zero_le _)
    obtain ⟨g, hu, hsing⟩ := exists_normalize_subspace 0 q P hs hb
    have hd := Submodule.finrank_mono
      (base_singular_axis_bound q (P.map (fixedLinearHom 0 q g).toLinearMap) hsing hu)
    rw [finrank_span_singleton (firstAxis_nonzero 0 q), LinearEquiv.finrank_map_eq] at hd
    exact hd
  | succ n ih =>
    intro P hs
    by_cases hb : P = ⊥
    · subst P
      exact (finrank_bot (fixedField q) (fixedSpace (n + 1) q)).le.trans (Nat.zero_le _)
    obtain ⟨g, hu, hsing⟩ := exists_normalize_subspace (n + 1) q P hs hb
    let A := P.map (fixedLinearHom (n + 1) q g).toLinearMap
    have huA : fixedFirst n q ∈ A := hu
    have htail := tail_singular n q A hsing huA
    have hdim := tail_finrank n q A hsing huA
    have hbound := ih (A.map (tailLinear n q)) htail
    have hA : Module.finrank (fixedField q) A = Module.finrank (fixedField q) P :=
      (fixedLinearHom (n + 1) q g).finrank_map_eq P
    omega

theorem original_rank_singular_finrank_le (s : ℕ) (q : CFSG.PrimePower)
    (P : Submodule (fixedField q) (fixedSpace (s + 2) q))
    (hs : ∀ x ∈ P, fixedQuadraticForm (s + 2) q x = 0) :
    Module.finrank (fixedField q) P ≤ s + 3 := singular_finrank_le q (s + 2) P hs

end SymmetricSubgroupAsymptotics.CFSGTwistedDSingularDimensionBound
