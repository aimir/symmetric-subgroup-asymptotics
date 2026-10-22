import SymmetricSubgroupAsymptotics.CliffordRestriction
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Nat.Prime.Basic

/-! Actual modular Clifford constituents have dimension dividing the
original dimension. In prime dimension the restriction is irreducible,
unless it has a one-dimensional constituent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra DirectSum

namespace SymmetricSubgroupAsymptotics.CFSGCliffordConstituentDimension

variable {k G V : Type} [Field k] [Group G] [Finite G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  (rho : Representation k G V) (H : Subgroup G) [H.Normal]

theorem constituent_finrank_dvd
    (hrho : Representation.IsIrreducible rho)
    (W : Subrepresentation (rho.comp H.subtype))
    (hW : Representation.IsIrreducible W.toRepresentation) :
    Module.finrank k W.toSubmodule ∣ Module.finrank k V := by
  obtain ⟨n, g, hinternal, _, _, _⟩ :=
    Theory.Representation.isaacs_theorem_6_5.{0, 0, 0, 0} rho H hrho W hW
  let rhoH : Representation k H V := rho.comp H.subtype
  let A : Fin n → Submodule k[H] rhoH.asModule := fun i =>
    (Theory.Representation.conjugateSubrepresentation rho H W (g i)).asSubmodule
  letI : FiniteDimensional k rhoH.asModule :=
    FiniteDimensional.of_injective rhoH.asModuleEquiv.toLinearMap
      rhoH.asModuleEquiv.injective
  letI : ∀ i : Fin n, FiniteDimensional k (A i) := fun i =>
    FiniteDimensional.of_injective ((A i).subtype.restrictScalars k)
      (A i).subtype_injective
  let e : (⨁ i : Fin n, A i) ≃ₗ[k[H]] rhoH.asModule :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hinternal
  have hd (i : Fin n) : Module.finrank k (A i) = Module.finrank k W.toSubmodule := by
    exact (Theory.Representation.conjugateSubrepresentationEquiv
      rho H W (g i)).toLinearEquiv.finrank_eq
  have hdim : Module.finrank k V = n * Module.finrank k W.toSubmodule := by
    calc
      Module.finrank k V = Module.finrank k (⨁ i : Fin n, A i) :=
        ((e.restrictScalars k).trans rhoH.asModuleEquiv).finrank_eq.symm
      _ = ∑ i : Fin n, Module.finrank k (A i) := Module.finrank_directSum k (fun i => A i)
      _ = ∑ _i : Fin n, Module.finrank k W.toSubmodule :=
        Finset.sum_congr rfl (fun i _ => hd i)
      _ = n * Module.finrank k W.toSubmodule := by simp
  rw [hdim]
  exact dvd_mul_left _ _

theorem restriction_irreducible_or_one_dimensional
    (hrho : Representation.IsIrreducible rho)
    (hp : (Module.finrank k V).Prime) :
    Representation.IsIrreducible (rho.comp H.subtype) ∨
      ∃ W : Subrepresentation (rho.comp H.subtype),
        Representation.IsIrreducible W.toRepresentation ∧
          Module.finrank k W.toSubmodule = 1 := by
  letI : Representation.IsIrreducible rho := hrho
  letI : Nontrivial V := Subrepresentation.irreducible_module_nontrivial rho
  obtain ⟨W, hW⟩ :=
    Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
      (rho.comp H.subtype)
  rcases (Nat.dvd_prime hp).mp (constituent_finrank_dvd rho H hrho W hW) with hd | hd
  · exact Or.inr ⟨W, hW, hd⟩
  · have htop : W = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      exact Submodule.eq_top_of_finrank_eq hd
    apply Or.inl
    apply isSimpleOrder_iff_isAtom_top.mpr
    simpa only [htop] using (Subrepresentation.irreducible_iff_isAtom W).mp hW

end SymmetricSubgroupAsymptotics.CFSGCliffordConstituentDimension
