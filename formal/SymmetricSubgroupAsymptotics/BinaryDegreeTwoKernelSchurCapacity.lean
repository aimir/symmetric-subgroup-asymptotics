import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoRelativeKernelOrbitAnchor
import SymmetricSubgroupAsymptotics.Non2SchurRowDegrees

/-!
# A degree-two kernel bound closes a twelve-dimensional binary module

The actual source has dimension at most twelve and fixed rank at most
four. An actual quotient of dimension at most four leaves only the scalar
degree-two type to check in its kernel. Multiplicity two there suffices:
the same type occurs at most twice in the quotient. Every larger Schur
product degree is bounded directly by the source dimension.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

local instance finiteDimensionalDegreeTwoKernelSubmodule
    {k R A : Type} [Field k] [Ring R] [Algebra k R]
    [AddCommGroup A] [Module R A] [Module k A] [IsScalarTower k R A]
    [FiniteDimensional k A] (S : Submodule R A) : FiniteDimensional k S :=
  FiniteDimensional.of_injective
    (S.subtype.restrictScalars k) S.subtype_injective

theorem representationSchurCapacity_le_four_of_degreeTwo_kernel
    {G V W : Type} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (rho : Representation (ZMod 2) G V) (tau : Representation (ZMod 2) G W)
    (q : rho.IntertwiningMap tau) (hq : Function.Surjective q)
    (hdim : Module.finrank (ZMod 2) V ≤ 12)
    (hfixed : Module.finrank (ZMod 2) rho.invariants ≤ 4)
    (himage : Module.finrank (ZMod 2) W ≤ 4)
    (hkernel : ∀ S : Submodule (ZMod 2)[G] rho.asModule,
      [IsSimpleModule (ZMod 2)[G] S] →
      ¬ representationSubmoduleFixed rho S → schurSimpleProductDegree rho S = 2 →
      schurSocleMultiplicity (k := ZMod 2) (R := (ZMod 2)[G])
        (A := q.ker.asSubmodule) (X := S) ≤ 2) :
    representationSchurCapacity rho ≤ 4 := by
  letI : FiniteDimensional (ZMod 2) q.ker.asSubmodule := FiniteDimensional.of_injective
    (q.ker.asSubmodule.subtype.restrictScalars (ZMod 2)) q.ker.asSubmodule.subtype_injective
  apply Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.representationSchurCapacity_le_of_fixed_nonfixed_multiplicity
    rho 4 hfixed
  intro S _hS hnonfixed
  letI : FiniteDimensional (ZMod 2) S := FiniteDimensional.of_injective
    (S.subtype.restrictScalars (ZMod 2)) S.subtype_injective
  letI : Nontrivial S := IsSimpleModule.nontrivial (ZMod 2)[G] S
  by_cases htwo : schurSimpleProductDegree rho S = 2
  · obtain ⟨hSdim, hSend⟩ := schurSimpleProductDegree_eq_two_profile rho S hnonfixed htwo
    have htarget : schurSocleMultiplicity (k := ZMod 2) (R := (ZMod 2)[G])
        (A := tau.asModule) (X := S) ≤ 2 := by
      have h := finrank_mul_schurSocleMultiplicity_le
        (k := ZMod 2) (R := (ZMod 2)[G]) (A := tau.asModule) (X := S)
      rw [hSdim, tau.asModuleEquiv.finrank_eq] at h
      omega
    have h := representationSchurMultiplicity_le_kernel_add_target (X := S) rho tau q hq
    have hk := hkernel S hnonfixed htwo
    rw [hSend]
    omega
  · have hdegree : 3 ≤ schurSimpleProductDegree rho S := by
      have h := two_le_schurSimpleProductDegree_of_nonfixed rho S hnonfixed
      omega
    have hoccupied := finrank_mul_schurSocleMultiplicity_le
      (k := ZMod 2) (R := (ZMod 2)[G]) (A := rho.asModule) (X := S)
    rw [rho.asModuleEquiv.finrank_eq] at hoccupied
    have hprod : 12 ≤ Module.finrank (ZMod 2) S *
        (4 * Module.finrank (Module.End (ZMod 2)[G] S) S) := by
      have h := Nat.mul_le_mul_left 4 hdegree
      simpa only [schurSimpleProductDegree, Nat.mul_left_comm] using h
    exact Nat.le_of_mul_le_mul_left ((hoccupied.trans hdim).trans hprod)
      (Module.finrank_pos (R := ZMod 2) (M := S))

end SymmetricSubgroupAsymptotics

end
