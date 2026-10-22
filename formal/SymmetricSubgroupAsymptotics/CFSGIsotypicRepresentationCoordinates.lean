import SymmetricSubgroupAsymptotics.RepresentationCoordinateHeads
import SymmetricSubgroupAsymptotics.External.Clifford.SubrepresentationLattice
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RepresentationTheory.Irreducible

/-! Isotypic coordinates with an actual irreducible subrepresentation of
the original carrier. The module/representation equivalences are kept
explicit, including their scalar-restriction instances. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.CFSGIsotypicRepresentationCoordinates

theorem exists_irreducible_coordinates
    {k S V : Type} [Field k] [Group S] [AddCommGroup V] [Module k V]
    [Finite V] [Nontrivial V]
    (rho : Representation k S V)
    (hss : IsSemisimpleModule k[S] rho.asModule) (hiso : IsIsotypic k[S] rho.asModule) :
    ∃ (n : ℕ) (U : Subrepresentation rho), 0 < n ∧
      Representation.IsIrreducible U.toRepresentation ∧
      ∃ e : V ≃ₗ[k] (Fin n → U.toSubmodule),
        (∀ (s : S) (v : V) (i : Fin n),
          e (rho s v) i = U.toRepresentation s (e v i)) := by
  letI : Finite rho.asModule :=
    Finite.of_injective rho.asModuleEquiv rho.asModuleEquiv.injective
  letI : Nontrivial rho.asModule := rho.asModuleEquiv.toEquiv.nontrivial
  letI : Module.Finite k[S] rho.asModule := Module.Finite.of_finite
  letI : IsSemisimpleModule k[S] rho.asModule := hss
  obtain ⟨n, hn, A, hA, ⟨f⟩⟩ := hiso.linearEquiv_fun
  let U : Subrepresentation rho := Subrepresentation.ofSubmodule' A
  let tau := U.toRepresentation
  have hU : Representation.IsIrreducible tau := by
    apply (Subrepresentation.irreducible_iff_isAtom U).mpr
    apply (Subrepresentation.subrepresentationSubmoduleOrderIso.isAtom_iff U).mp
    change IsAtom A
    exact isSimpleModule_iff_isAtom.mp hA
  let F : rho.asModule ≃ₗ[k[S]] (Fin n → tau.asModule) :=
    f.trans (LinearEquiv.piCongrRight (fun _ => submoduleRepresentationModuleEquiv rho A))
  let e : V ≃ₗ[k] (Fin n → U.toSubmodule) :=
    rho.asModuleEquiv.symm.trans ((F.restrictScalars k).trans
      (LinearEquiv.piCongrRight (fun _ => tau.asModuleEquiv)))
  refine ⟨n, U, Nat.pos_of_ne_zero hn.out, hU, e, ?_⟩
  intro s v i
  change tau.asModuleEquiv (F (rho.asModuleEquiv.symm (rho s v)) i) =
    tau s (tau.asModuleEquiv (F (rho.asModuleEquiv.symm v) i))
  rw [Representation.asModuleEquiv_symm_map_rho, map_smul]
  change tau.asModuleEquiv ((MonoidAlgebra.of k S s) • F (rho.asModuleEquiv.symm v) i) = _
  rw [Representation.asModuleEquiv_map_smul]
  simp only [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single_one]

theorem constituent_injective_of_coordinates
    {k S V W : Type} [Field k] [Group S]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {n : ℕ} (rho : Representation k S V) (tau : Representation k S W)
    (hf : Function.Injective rho) (e : V ≃ₗ[k] (Fin n → W))
    (he : ∀ s v i, e (rho s v) i = tau s (e v i)) : Function.Injective tau := by
  intro a b hab
  apply hf
  apply LinearMap.ext
  intro v
  apply e.injective
  funext i
  rw [he, he]
  exact LinearMap.congr_fun hab (e v i)

end SymmetricSubgroupAsymptotics.CFSGIsotypicRepresentationCoordinates
