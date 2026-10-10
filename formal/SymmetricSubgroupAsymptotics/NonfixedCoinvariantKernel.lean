import SymmetricSubgroupAsymptotics.RepresentationCoinvariantFiniteCertificate
import SymmetricSubgroupAsymptotics.RepresentationSchurRows
import SymmetricSubgroupAsymptotics.SchurMultiplicity

/-!
# Nonfixed simple maps land in the coinvariant kernel

The quotient of a representation by its intrinsic displacement space is
pointwise fixed.  A map from a nonfixed simple module to that quotient is
therefore zero.  Consequently every map from that simple module into the
original representation lands in the literal coinvariant kernel.

This is useful with finite displacement certificates: the certificate need
only identify and bound the kernel state, rather than classify simple modules
in every ambient state separately.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

universe u

variable {k G V A : Type u} [Field k] [Group G]
  [AddCommGroup V] [Module k V]
  [AddCommGroup A] [Module k A]

/-- The intrinsic displacement space, with the action inherited from the
original representation. -/
def representationCoinvariantsKernelSubrepresentation
    (rho : Representation k G V) : Subrepresentation rho where
  toSubmodule := Representation.Coinvariants.ker rho
  apply_mem_toSubmodule := representationCoinvariantsKer_apply_mem rho

/-- The canonical coinvariant quotient map is an intertwiner to a trivial
representation on the quotient vector space. -/
noncomputable def representationCoinvariantsIntertwiner
    (rho : Representation k G V) :
    rho.IntertwiningMap
      (Representation.trivial k G rho.Coinvariants) where
  toLinearMap := Representation.Coinvariants.mk rho
  isIntertwining' := by
    intro g
    apply LinearMap.ext
    intro v
    change Representation.Coinvariants.mk rho (rho g v) =
      Representation.Coinvariants.mk rho v
    exact Representation.Coinvariants.mk_self_apply rho g v

/-- Every equivariant map from a nonfixed simple row into `rho` has image in
the intrinsic coinvariant kernel of `rho`. -/
theorem schurHom_apply_mem_coinvariantsKer_of_nonfixed
    (sigma : Representation k G A)
    (S : Submodule k[G] sigma.asModule)
    [IsSimpleModule k[G] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (rho : Representation k G V)
    (f : S →ₗ[k[G]] rho.asModule)
    (x : S) :
    rho.asModuleEquiv (f x) ∈ Representation.Coinvariants.ker rho := by
  let qI := representationCoinvariantsIntertwiner rho
  let qR : rho.asModule →ₗ[k[G]]
      (Representation.trivial k G rho.Coinvariants).asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule
      rho (Representation.trivial k G rho.Coinvariants) qI
  let q : S →ₗ[k[G]]
      (Representation.trivial k G rho.Coinvariants).asModule := qR.comp f
  have hqzero : q = 0 := by
    by_contra hq
    have hqinj : Function.Injective q := LinearMap.injective_of_ne_zero hq
    apply hnonfixed
    intro g y
    apply hqinj
    calc
      q (MonoidAlgebra.single g (1 : k) • y) =
          MonoidAlgebra.single g (1 : k) • q y := q.map_smul _ _
      _ = q y := by
        apply (Representation.trivial k G rho.Coinvariants).asModuleEquiv.injective
        rw [Representation.asModuleEquiv_map_smul,
          Representation.asAlgebraHom_single, one_smul]
        rfl
  apply (Representation.Coinvariants.mk_eq_zero rho).mp
  have hx := LinearMap.congr_fun hqzero x
  change Representation.Coinvariants.mk rho (rho.asModuleEquiv (f x)) = 0 at hx
  exact hx

/-- Corestrict every nonfixed simple-source map to the intrinsic
coinvariant-kernel module. -/
noncomputable def schurHomCoinvariantsKernelCorestrict
    (sigma : Representation k G A)
    (S : Submodule k[G] sigma.asModule)
    [IsSimpleModule k[G] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (rho : Representation k G V) :
    (S →ₗ[k[G]] rho.asModule) →ₗ[k]
      (S →ₗ[k[G]]
        (representationCoinvariantsKernelSubrepresentation rho).asSubmodule) where
  toFun f := f.codRestrict _ (fun x ↦ by
    change rho.asModuleEquiv (f x) ∈ Representation.Coinvariants.ker rho
    exact schurHom_apply_mem_coinvariantsKer_of_nonfixed
      sigma S hnonfixed rho f x)
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl

theorem schurHomCoinvariantsKernelCorestrict_injective
    (sigma : Representation k G A)
    (S : Submodule k[G] sigma.asModule)
    [IsSimpleModule k[G] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (rho : Representation k G V) :
    Function.Injective
      (schurHomCoinvariantsKernelCorestrict sigma S hnonfixed rho) := by
  intro f g hfg
  apply LinearMap.ext
  intro x
  exact congrArg Subtype.val
    (DFunLike.congr_fun hfg x)

/-- A nonfixed simple row occurs no more often in a representation than in
its intrinsic displacement kernel. -/
theorem schurSocleMultiplicity_le_coinvariantsKernel_of_nonfixed
    [FiniteDimensional k V]
    (sigma : Representation k G A)
    (S : Submodule k[G] sigma.asModule)
    [FiniteDimensional k S]
    [IsSimpleModule k[G] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (rho : Representation k G V) :
    schurSocleMultiplicity
        (k := k) (R := k[G]) (A := rho.asModule) (X := S) ≤
      schurSocleMultiplicity
        (k := k) (R := k[G])
        (A := (representationCoinvariantsKernelSubrepresentation rho).asSubmodule)
        (X := S) := by
  let K := representationCoinvariantsKernelSubrepresentation rho
  letI : FiniteDimensional k K.asSubmodule :=
    FiniteDimensional.of_injective
      (K.asSubmodule.subtype.restrictScalars k) K.asSubmodule.subtype_injective
  have hhom :=
    (schurHomCoinvariantsKernelCorestrict sigma S hnonfixed rho).
      finrank_le_finrank_of_injective
        (schurHomCoinvariantsKernelCorestrict_injective
          sigma S hnonfixed rho)
  rw [schurHom_finrank_eq_multiplicity
        (k := k) (R := k[G]) (A := rho.asModule) (X := S),
    schurHom_finrank_eq_multiplicity
        (k := k) (R := k[G]) (A := K.asSubmodule) (X := S)] at hhom
  apply Nat.le_of_mul_le_mul_right hhom
  letI : Nontrivial S := IsSimpleModule.nontrivial k[G] S
  exact Module.finrank_pos (R := k) (M := Module.End k[G] S)

end SymmetricSubgroupAsymptotics

end
