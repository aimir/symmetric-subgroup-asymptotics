import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedTailLinear
import SymmetricSubgroupAsymptotics.CFSGTwistedDHighestPairOperator
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailQuadratic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! A Q-singular subspace containing the first fixed singular axis
has a SAME-fixed-field singular tail of dimension exactly one less.
This is the literal induction step for the nonsplit Witt bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDSingularTailDimension
open CFSGOrthogonalDSerreMatrices CFSGTwistedDFixedQuadraticSpace
open CFSGTwistedDFixedTailLinear CFSGTwistedA2FixedField CFSGTwistedDHighestPairOperator
open CFSGOrthogonalDIndexTailCoordinates CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexPrefixPerpendicular CFSGOrthogonalDGenerationForkTorus

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

private theorem zero_ne_last (n : ℕ) : (0 : Fin (n + 3)) ≠ last (n + 1) := by
  intro h
  have hv := congrArg Fin.val h
  change 0 = n + 2 at hv
  omega

def fixedFirst (n : ℕ) (q : CFSG.PrimePower) : fixedSpace (n + 1) q :=
  positiveBasis (n + 1) q 0 (zero_ne_last n)

theorem fixedFirst_nonzero (n : ℕ) (q : CFSG.PrimePower) : fixedFirst n q ≠ 0 := by
  intro h
  have he := congrArg (fun v : fixedSpace (n + 1) q => v.val (Sum.inl 0)) h
  change (Pi.single (Sum.inl (0 : Fin (n + 3))) (1 : q.Extension 2) :
    Index (n + 3) → q.Extension 2) (Sum.inl 0) = 0 at he
  rw [Pi.single_eq_same] at he
  exact one_ne_zero he

theorem tail_fixedFirst_zero (n : ℕ) (q : CFSG.PrimePower) :
    tailLinear n q (fixedFirst n q) = 0 := by
  apply Subtype.ext
  funext i
  cases i <;> simp [tailLinear, tailRestriction, tailIndex, fixedFirst, positiveBasis]

theorem negativeHead_zero (n : ℕ) (q : CFSG.PrimePower)
    (P : Submodule (fixedField q) (fixedSpace (n + 1) q))
    (hs : ∀ x ∈ P, fixedQuadraticForm (n + 1) q x = 0)
    (hu : fixedFirst n q ∈ P) (v : fixedSpace (n + 1) q) (hv : v ∈ P) :
    negativeHead n q v = 0 := by
  have hp : (fixedQuadraticForm (n + 1) q).polarBilin (fixedFirst n q) v = 0 := by
    change fixedQuadraticForm (n + 1) q (fixedFirst n q + v) -
      fixedQuadraticForm (n + 1) q (fixedFirst n q) - fixedQuadraticForm (n + 1) q v = 0
    rw [hs _ (P.add_mem hu hv), hs _ hu, hs _ hv]
    ring
  have he := congrArg (fun a : fixedField q => (a : q.Extension 2)) hp
  dsimp only at he
  rw [fixedQuadraticForm_polar, splitQuadraticForm_polar] at he
  change CFSGOrthogonalDIndexPolarForm.polar (q.Extension 2)
    (Pi.single (Sum.inl (0 : Fin (n + 3))) 1) v.val = 0 at he
  rw [polar_positive_basis] at he
  apply Subtype.ext
  change v.val (Sum.inr 0) = 0
  exact he

theorem tail_singular (n : ℕ) (q : CFSG.PrimePower)
    (P : Submodule (fixedField q) (fixedSpace (n + 1) q))
    (hs : ∀ x ∈ P, fixedQuadraticForm (n + 1) q x = 0)
    (hu : fixedFirst n q ∈ P) :
    ∀ x ∈ P.map (tailLinear n q), fixedQuadraticForm n q x = 0 := by
  rintro x ⟨v, hv, rfl⟩
  have he := hs v hv
  rw [quadratic_coordinates, negativeHead_zero n q P hs hu v hv, mul_zero, zero_add] at he
  exact he

theorem tail_finrank (n : ℕ) (q : CFSG.PrimePower)
    (P : Submodule (fixedField q) (fixedSpace (n + 1) q))
    (hs : ∀ x ∈ P, fixedQuadraticForm (n + 1) q x = 0)
    (hu : fixedFirst n q ∈ P) :
    Module.finrank (fixedField q) (P.map (tailLinear n q)) + 1 = Module.finrank (fixedField q) P := by
  let f := (tailLinear n q).comp P.subtype
  have hk : f.ker.map P.subtype = Submodule.span (fixedField q) {fixedFirst n q} := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      change tailLinear n q x.val = 0 at hx
      have ht := congrArg (fun z : fixedSpace n q => z.val) hx
      change tailRestriction (q.Extension 2) (n + 2) x.val.val = 0 at ht
      have hn := congrArg (fun a : fixedField q => (a : q.Extension 2))
        (negativeHead_zero n q P hs hu x.val x.property)
      change x.val.val (Sum.inr 0) = 0 at hn
      have he := vector_eq_first_of_tail_zero (q.Extension 2) (n + 2) x.val.val ht hn
      have heF : x.val = positiveHead n q x.val • fixedFirst n q := Subtype.ext he
      exact Submodule.mem_span_singleton.mpr ⟨positiveHead n q x.val, heF.symm⟩
    · intro hv
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
      refine ⟨⟨c • fixedFirst n q, P.smul_mem c hu⟩, ?_, rfl⟩
      change tailLinear n q (c • fixedFirst n q) = 0
      rw [map_smul, tail_fixedFirst_zero, smul_zero]
  have hker : Module.finrank (fixedField q) f.ker = 1 :=
    (Submodule.finrank_map_subtype_eq P f.ker).symm.trans
      ((congrArg (fun T : Submodule (fixedField q) (fixedSpace (n + 1) q) =>
        Module.finrank (fixedField q) T) hk).trans
          (finrank_span_singleton (fixedFirst_nonzero n q)))
  have hr : f.range = P.map (tailLinear n q) := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hd := LinearMap.finrank_range_add_finrank_ker (K := fixedField q)
    (V := P) (V₂ := fixedSpace n q) f
  rw [hr, hker] at hd
  exact hd

end SymmetricSubgroupAsymptotics.CFSGTwistedDSingularTailDimension
