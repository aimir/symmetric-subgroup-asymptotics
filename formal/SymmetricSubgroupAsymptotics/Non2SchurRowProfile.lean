import SymmetricSubgroupAsymptotics.RepresentationSchurRows
import Mathlib.Tactic.FieldSimp

/-!
# Exact numerical profile of one nonfixed Schur row

For an actual simple submodule `S`, the manuscript uses
`h = dim_k S`, `d = dim_End(S) S`, and the socle multiplicity `m`.
Its Schur density is `m/d`, while the mixed trivial/simple section has
dimension `t+h*m`.  This file records the exact identity
`(h*d) * density = mixedDimension - t`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

universe u
variable {k B A : Type u} [Field k] [Group B]
    [AddCommGroup A] [Module k A]

def schurSimpleProductDegree
    (σ : Representation k B A) (S : Submodule k[B] σ.asModule)
    [IsSimpleModule k[B] S] : Nat :=
  Module.finrank k S * Module.finrank (Module.End k[B] S) S

def schurMixedSocleDimension
    [FiniteDimensional k A]
    (σ : Representation k B A) (S : Submodule k[B] σ.asModule)
    [IsSimpleModule k[B] S] (t : Nat) : Nat :=
  t + Module.finrank k S *
    schurSocleMultiplicity (k := k) (R := k[B])
      (A := σ.asModule) (X := S)

theorem schurSimpleRatio_nonneg
    [FiniteDimensional k A]
    (σ : Representation k B A) (S : Submodule k[B] σ.asModule)
    [IsSimpleModule k[B] S] :
    0 ≤ (Module.finrank k (S →ₗ[k[B]] σ.asModule) : ℝ) /
      Module.finrank k S := by
  positivity

/-- Exact conversion from the intrinsic Hom density to the mixed-section
dimension used in every branch of the coupled socle estimate. -/
theorem schurSimpleProductDegree_mul_ratio
    [FiniteDimensional k A]
    (σ : Representation k B A) (S : Submodule k[B] σ.asModule)
    [IsSimpleModule k[B] S] (t : Nat) :
    (schurSimpleProductDegree σ S : ℝ) *
        ((Module.finrank k (S →ₗ[k[B]] σ.asModule) : ℝ) /
          Module.finrank k S) =
      (schurMixedSocleDimension σ S t : ℝ) - t := by
  classical
  let h := Module.finrank k S
  let d := Module.finrank (Module.End k[B] S) S
  let m := schurSocleMultiplicity (k := k) (R := k[B])
    (A := σ.asModule) (X := S)
  letI : FiniteDimensional k S := FiniteDimensional.of_injective
    (S.subtype.restrictScalars k) S.subtype_injective
  haveI : Nontrivial S := IsSimpleModule.nontrivial k[B] S
  have hdNat : 0 < d := by
    have htower := schur_simple_finrank_tower
      (k := k) (R := k[B]) (X := S)
    change h = Module.finrank k (Module.End k[B] S) * d at htower
    have hh : 0 < h := Module.finrank_pos (R := k) (M := S)
    by_contra hd
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    rw [hd0, Nat.mul_zero] at htower
    omega
  have hd : (d : ℝ) ≠ 0 := by
    exact_mod_cast hdNat.ne'
  rw [schurSimpleRatio_eq_multiplicity_division
    (k := k) (R := k[B]) (A := σ.asModule) (X := S)]
  change ((h * d : Nat) : ℝ) * ((m : ℝ) / d) =
    ((t + h * m : Nat) : ℝ) - t
  push_cast
  field_simp
  ring

end SymmetricSubgroupAsymptotics

end
