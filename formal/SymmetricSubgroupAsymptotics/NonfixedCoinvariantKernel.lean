import SymmetricSubgroupAsymptotics.RepresentationCoinvariantFiniteCertificate
import SymmetricSubgroupAsymptotics.RepresentationCoordinateHeads
import SymmetricSubgroupAsymptotics.RepresentationSchurRows
import SymmetricSubgroupAsymptotics.SchurMultiplicity
import SymmetricSubgroupAsymptotics.SchurMultiplicityTargetEquiv

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

/-- An injective target intertwiner can only increase every simple-source
Schur multiplicity. -/
theorem schurSocleMultiplicity_le_of_injective_intertwiner
    {W : Type u} [AddCommGroup W] [Module k W]
    [FiniteDimensional k V] [FiniteDimensional k W]
    (rho : Representation k G V) (tau : Representation k G W)
    (i : rho.IntertwiningMap tau) (hi : Function.Injective i)
    {X : Type u} [AddCommGroup X] [Module k X]
    [Module k[G] X] [IsScalarTower k k[G] X]
    [FiniteDimensional k X] [IsSimpleModule k[G] X] :
    schurSocleMultiplicity
        (k := k) (R := k[G]) (A := rho.asModule) (X := X) ≤
      schurSocleMultiplicity
        (k := k) (R := k[G]) (A := tau.asModule) (X := X) := by
  let iR : rho.asModule →ₗ[k[G]] tau.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule rho tau i
  let post : (X →ₗ[k[G]] rho.asModule) →ₗ[k]
      (X →ₗ[k[G]] tau.asModule) where
    toFun f := iR.comp f
    map_add' f g := by ext x; rfl
    map_smul' c f := by ext x; rfl
  have hpost : Function.Injective post := by
    intro f g hfg
    apply LinearMap.ext
    intro x
    apply hi
    exact DFunLike.congr_fun hfg x
  have hhom := post.finrank_le_finrank_of_injective hpost
  rw [schurHom_finrank_eq_multiplicity
        (k := k) (R := k[G]) (A := rho.asModule) (X := X),
    schurHom_finrank_eq_multiplicity
        (k := k) (R := k[G]) (A := tau.asModule) (X := X)] at hhom
  apply Nat.le_of_mul_le_mul_right hhom
  letI : Nontrivial X := IsSimpleModule.nontrivial k[G] X
  exact Module.finrank_pos (R := k) (M := Module.End k[G] X)

/-- To bound a nonfixed row of `rho`, it is enough to inject its intrinsic
displacement kernel into a certified target representation. -/
theorem schurSocleMultiplicity_le_of_nonfixed_coinvariantsKernel_injection
    [FiniteDimensional k V]
    (sigma : Representation k G A)
    (S : Submodule k[G] sigma.asModule)
    [FiniteDimensional k S]
    [IsSimpleModule k[G] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (rho : Representation k G V)
    {W : Type u} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W]
    (tau : Representation k G W)
    (i : (representationCoinvariantsKernelSubrepresentation rho).
      toRepresentation.IntertwiningMap tau)
    (hi : Function.Injective i) :
    schurSocleMultiplicity
        (k := k) (R := k[G]) (A := rho.asModule) (X := S) ≤
      schurSocleMultiplicity
        (k := k) (R := k[G]) (A := tau.asModule) (X := S) := by
  let K := representationCoinvariantsKernelSubrepresentation rho
  have hkernel := schurSocleMultiplicity_le_of_injective_intertwiner
    K.toRepresentation tau i hi (X := S)
  have heq := schurSocleMultiplicity_eq_of_target_linearEquiv
    (k := k) (R := k[G]) (X := S)
      (submoduleRepresentationModuleEquiv rho K.asSubmodule)
  exact (schurSocleMultiplicity_le_coinvariantsKernel_of_nonfixed
    sigma S hnonfixed rho).trans (by
      rw [heq]
      exact hkernel)

/-- Every intertwiner carries intrinsic displacements to intrinsic
displacements.  This is the representation-level map on the nonfixed
part, before any quotient or finite-state identification is chosen. -/
noncomputable def coinvariantsKernelIntertwiner
    (rho : Representation k G V)
    {W : Type u} [AddCommGroup W] [Module k W]
    (tau : Representation k G W)
    (q : rho.IntertwiningMap tau) :
    (representationCoinvariantsKernelSubrepresentation rho).
        toRepresentation.IntertwiningMap
      (representationCoinvariantsKernelSubrepresentation tau).
        toRepresentation where
  toLinearMap :=
    { toFun := fun x => ⟨q x.1, by
          change q x.1 ∈ Representation.Coinvariants.ker tau
          rw [← Representation.Coinvariants.mk_eq_zero tau]
          rw [← Representation.Coinvariants.map_mk q x.1]
          rw [(Representation.Coinvariants.mk_eq_zero rho).mpr x.2,
            map_zero]⟩
      map_add' := by intro x y; exact Subtype.ext (map_add q x.1 y.1)
      map_smul' := by intro c x; exact Subtype.ext (map_smul q c x.1) }
  isIntertwining' := by
    intro g
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining rho tau q g x.1

/-- Right exactness of the intrinsic displacement space: a surjective
intertwiner maps the source coinvariant kernel onto the target one.  The
proof works on the literal spanning displacements, so it does not assume a
splitting of the quotient. -/
theorem coinvariantsKernelIntertwiner_surjective
    (rho : Representation k G V)
    {W : Type u} [AddCommGroup W] [Module k W]
    (tau : Representation k G W)
    (q : rho.IntertwiningMap tau)
    (hq : Function.Surjective q) :
    Function.Surjective (coinvariantsKernelIntertwiner rho tau q) := by
  intro y
  rcases y with ⟨y, hy⟩
  change y ∈ Submodule.span k
    (Set.range fun gx : G × W => tau gx.1 gx.2 - gx.2) at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨⟨g, w⟩, rfl⟩ := hy
      obtain ⟨v, rfl⟩ := hq w
      let x :
          (representationCoinvariantsKernelSubrepresentation rho).
            toRepresentation.asModule :=
        ⟨rho g v - v, Representation.Coinvariants.sub_mem_ker g v⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      change q (rho g v - v) = tau g (q v) - q v
      rw [map_sub, Representation.IntertwiningMap.isIntertwining]
  | zero =>
      exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', by simp⟩
  | smul c x _ hx =>
      obtain ⟨x', rfl⟩ := hx
      exact ⟨c • x', by simp⟩

end SymmetricSubgroupAsymptotics

end
