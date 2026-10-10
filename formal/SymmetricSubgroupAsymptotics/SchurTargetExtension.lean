import SymmetricSubgroupAsymptotics.SchurMultiplicity
import SymmetricSubgroupAsymptotics.SchurMultiplicityTargetEquiv
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Schur multiplicities across an actual target extension

For a submodule `K <= A`, composition with `A -> A/K` has kernel exactly
`Hom(X,K)`.  Rank-nullity therefore bounds the multiplicity of a simple
type in `A` by the sum of its multiplicities in `K` and `A/K`.  This is the
formal version of the additive `m_E + m_T` step in the fixed-frame socle
filtration.  No splitting of the original group extension is used.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

universe u

variable {k R A X : Type u} [Field k] [Ring R] [Algebra k R]
  [AddCommGroup A] [Module R A] [Module k A] [IsScalarTower k R A]
  [AddCommGroup X] [Module R X] [Module k X] [IsScalarTower k R X]

/-- Postcompose a simple-source map with the literal quotient by `K`. -/
def schurHomTargetQuotient (K : Submodule R A) :
    (X →ₗ[R] A) →ₗ[k] (X →ₗ[R] A ⧸ K) where
  toFun f := K.mkQ.comp f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The kernel of target quotient is the Hom space into the actual
submodule. -/
def schurHomTargetQuotientKernelEquiv (K : Submodule R A) :
    LinearMap.ker (schurHomTargetQuotient (k := k) (X := X) K) ≃ₗ[k]
      (X →ₗ[R] K) where
  toFun f := f.1.codRestrict K (fun x => by
    have hx := LinearMap.congr_fun f.2 x
    change K.mkQ (f.1 x) = 0 at hx
    exact (Submodule.Quotient.mk_eq_zero K).mp hx)
  invFun f := ⟨K.subtype.comp f, by
    ext x
    change K.mkQ (f x : A) = 0
    exact (Submodule.Quotient.mk_eq_zero K).mpr (f x).2⟩
  left_inv f := by
    apply Subtype.ext
    ext x
    rfl
  right_inv f := by
    ext x
    rfl
  map_add' _ _ := by
    ext x
    rfl
  map_smul' _ _ := by
    ext x
    rfl

/-- Target left-exactness in finite dimension. -/
theorem schurHom_target_finrank_le_submodule_quotient
    [FiniteDimensional k A] [FiniteDimensional k X]
    (K : Submodule R A)
    [FiniteDimensional k K] [FiniteDimensional k (A ⧸ K)] :
    Module.finrank k (X →ₗ[R] A) ≤
      Module.finrank k (X →ₗ[R] K) +
        Module.finrank k (X →ₗ[R] A ⧸ K) := by
  letI : FiniteDimensional k K := FiniteDimensional.of_injective
    (K.subtype.restrictScalars k) K.subtype_injective
  letI : FiniteDimensional k (A ⧸ K) := FiniteDimensional.of_surjective
    (K.mkQ.restrictScalars k) K.mkQ_surjective
  have h := LinearMap.finrank_range_add_finrank_ker
    (schurHomTargetQuotient (k := k) (X := X) K)
  rw [(schurHomTargetQuotientKernelEquiv
    (k := k) (X := X) K).finrank_eq] at h
  have hr := Submodule.finrank_le
    (LinearMap.range (schurHomTargetQuotient (k := k) (X := X) K))
  omega

/-- A simple type's actual socle multiplicity is additive up to inequality
across every literal target submodule.  The common Schur-ring dimension is
cancelled only after rank-nullity, so no absolute-irreducibility premise is
introduced. -/
theorem schurSocleMultiplicity_le_submodule_add_quotient
    [FiniteDimensional k A] [FiniteDimensional k X]
    [IsSimpleModule R X]
    (K : Submodule R A)
    [FiniteDimensional k K] [FiniteDimensional k (A ⧸ K)] :
    schurSocleMultiplicity (k := k) (R := R) (A := A) (X := X) ≤
      schurSocleMultiplicity (k := k) (R := R) (A := K) (X := X) +
        schurSocleMultiplicity (k := k) (R := R) (A := A ⧸ K) (X := X) := by
  have h := schurHom_target_finrank_le_submodule_quotient
    (k := k) (X := X) K
  rw [schurHom_finrank_eq_multiplicity
        (k := k) (R := R) (A := A) (X := X),
    schurHom_finrank_eq_multiplicity
        (k := k) (R := R) (A := K) (X := X),
    schurHom_finrank_eq_multiplicity
        (k := k) (R := R) (A := A ⧸ K) (X := X)] at h
  have hfactor :
      schurSocleMultiplicity (k := k) (R := R) (A := A) (X := X) *
          Module.finrank k (Module.End R X) ≤
        (schurSocleMultiplicity (k := k) (R := R) (A := K) (X := X) +
          schurSocleMultiplicity (k := k) (R := R) (A := A ⧸ K) (X := X)) *
            Module.finrank k (Module.End R X) := by
    simpa only [Nat.add_mul] using h
  exact Nat.le_of_mul_le_mul_right hfactor (by
    letI : Nontrivial X := IsSimpleModule.nontrivial R X
    exact Module.finrank_pos (R := k) (M := Module.End R X))

/-- Schur multiplicity is subadditive across any surjective intertwiner,
using its literal invariant kernel and actual target representation. -/
theorem representationSchurMultiplicity_le_kernel_add_target
    {G V W : Type u} [Group G]
    [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    [FiniteDimensional k V] [FiniteDimensional k W]
    (rho : Representation k G V) (sigma : Representation k G W)
    (q : rho.IntertwiningMap sigma) (hq : Function.Surjective q)
    [Module k[G] X] [IsScalarTower k k[G] X]
    [FiniteDimensional k X] [IsSimpleModule k[G] X] :
    schurSocleMultiplicity
        (k := k) (R := k[G]) (A := rho.asModule) (X := X) ≤
      schurSocleMultiplicity
          (k := k) (R := k[G])
          (A := q.ker.asSubmodule) (X := X) +
        schurSocleMultiplicity
          (k := k) (R := k[G]) (A := sigma.asModule) (X := X) := by
  let f : rho.asModule →ₗ[k[G]] sigma.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule rho sigma q
  let K : Submodule k[G] rho.asModule := q.ker.asSubmodule
  have hK : K = f.ker := by
    ext v
    rfl
  let eQ : (rho.asModule ⧸ K) ≃ₗ[k[G]] sigma.asModule := by
    rw [hK]
    exact f.quotKerEquivOfSurjective hq
  have hmQ := schurSocleMultiplicity_eq_of_target_linearEquiv
    (k := k) (R := k[G]) (X := X) eQ
  have hm := schurSocleMultiplicity_le_submodule_add_quotient
    (k := k) (R := k[G]) (A := rho.asModule) (X := X) K
  rw [hmQ] at hm
  exact hm

/-- The ground-field dimension occupied by one simple isotypic row cannot
exceed the dimension of its actual target. -/
theorem finrank_mul_schurSocleMultiplicity_le
    [FiniteDimensional k A] [FiniteDimensional k X]
    [IsSimpleModule R X] :
    Module.finrank k X *
        schurSocleMultiplicity (k := k) (R := R) (A := A) (X := X) ≤
      Module.finrank k A := by
  let I := isotypicComponent R A X
  let e := schurSocleDecomposition
    (k := k) (R := R) (A := A) (X := X)
  have he := (e.restrictScalars k).finrank_eq
  have hI : Module.finrank k I =
      Module.finrank k X *
        schurSocleMultiplicity (k := k) (R := R) (A := A) (X := X) := by
    simpa only [Module.finrank_pi_fintype, Fintype.card_fin,
      Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul,
      Nat.mul_comm] using he
  rw [← hI]
  exact Submodule.finrank_le (I.restrictScalars k)

end SymmetricSubgroupAsymptotics

end
