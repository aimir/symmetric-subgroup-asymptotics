import SymmetricSubgroupAsymptotics.External.Clifford.Clifford
import SymmetricSubgroupAsymptotics.CliffordRawRestrictionInput

/-!
# Clifford restriction, proved over an arbitrary field

The ported Isaacs 6.5 decomposition is used on the literal normal subgroup.
Finite dimensionality supplies an irreducible constituent; the decomposition
then proves semisimplicity and conjugacy of every pair of constituent types.
In particular no characteristic-zero or Maschke hypothesis is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.CliffordRawRestriction

private theorem simple_asSubmodule
    {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (W : Subrepresentation rho)
    (hW : Representation.IsIrreducible W.toRepresentation) :
    IsSimpleModule k[G] W.asSubmodule := by
  apply isSimpleModule_iff_isAtom.mpr
  exact (Subrepresentation.subrepresentationSubmoduleOrderIso.isAtom_iff W).mpr
    ((Subrepresentation.irreducible_iff_isAtom W).mp hW)

/-- The complete raw Clifford interface is a theorem, including modular characteristic. -/
def proved : Input where
  semisimple := by
    intro k G V _ _ _ _ _ _ rho hrho H _
    letI : Representation.IsIrreducible rho := hrho
    letI : Nontrivial V := Subrepresentation.irreducible_module_nontrivial rho
    obtain ⟨W, hW⟩ :=
      Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
        (rho.comp H.subtype)
    obtain ⟨n, g, hinternal, hirred, _, _⟩ :=
      Theory.Representation.isaacs_theorem_6_5.{0, 0, 0, 0} rho H hrho W hW
    let A : Fin n → Submodule k[H] (Representation.asModule (rho.comp H.subtype)) := fun i =>
      (Theory.Representation.conjugateSubrepresentation rho H W (g i)).asSubmodule
    have hsimple (i : Fin n) : IsSimpleModule k[H] (A i) :=
      simple_asSubmodule _ _ (hirred i)
    exact isSemisimpleModule_of_isSemisimpleModule_submodule'
      (fun i => by letI := hsimple i; infer_instance) hinternal.submodule_iSup_eq_top
  conjugateTypes := by
    intro k G V _ _ _ _ _ _ rho hrho H _ S T hS hT
    obtain ⟨n, g, hinternal, hirred, hconj, _⟩ :=
      Theory.Representation.isaacs_theorem_6_5.{0, 0, 0, 0} rho H hrho S hS
    let A : Fin n → Submodule k[H] (Representation.asModule (rho.comp H.subtype)) := fun i =>
      (Theory.Representation.conjugateSubrepresentation rho H S (g i)).asSubmodule
    have hsimple (i : Fin n) : IsSimpleModule k[H] (A i) :=
      simple_asSubmodule _ _ (hirred i)
    let s : Set (Submodule k[H] (Representation.asModule (rho.comp H.subtype))) := Set.range A
    letI : ∀ m : s, IsSimpleModule k[H] m.1 := fun m => by
      obtain ⟨i, hi⟩ := m.2
      rw [← hi]
      exact hsimple i
    letI : IsSimpleModule k[H] T.asSubmodule := simple_asSubmodule _ _ hT
    have hs : sSup s = ⊤ := by
      simpa [s, sSup_range] using hinternal.submodule_iSup_eq_top
    obtain ⟨M, ⟨i, rfl⟩, he⟩ := T.asSubmodule.linearEquiv_of_sSup_eq_top s hs
    have hrep :=
      (Theory.Representation.isaacs_6_5_nonempty_repEquiv_iff_asSubmodule_linearEquiv
        T (Theory.Representation.conjugateSubrepresentation rho H S (g i))).mpr he
    refine ⟨g i, ?_⟩
    change Nonempty (Representation.Equiv
      (Theory.Representation.conjugateRep (G := G) (H := H) S.toRepresentation (g i))
      T.toRepresentation)
    exact ⟨Theory.Representation.RepEquiv.toRepresentationEquiv
      (hrep.some.trans (hconj i).some).symm⟩

end SymmetricSubgroupAsymptotics.CliffordRawRestriction
