import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RingTheory.SimpleModule.Isotypic

/-! The raw modular Clifford statement, without a wreath-action corollary.
Reference: G. M. Tracey, Minimal generation of transitive permutation groups
(PhD thesis, Warwick,2017), printedp14, Theorem2.3.1(i),(ii), Remark2.3.4:
https://wrap.warwick.ac.uk/id/eprint/97251/1/WRAP_Theses_Tracey_2017.pdf
The cited source there is Curtis--Reiner, Representation Theory of Finite
Groups and Associative Algebras, Theorem49.7. We use only finite groups
and finite-dimensional modules, which are within the stated theorem.
Neither faithful retained sections nor any original-action conclusion is
part of this interface. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.CliffordRawRestriction

structure Input : Prop where
  semisimple : ∀ {k G V : Type} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : Representation k G V),Representation.IsIrreducible rho →
    ∀ (H : Subgroup G) [H.Normal],
      IsSemisimpleModule k[H] (Representation.asModule (rho.comp H.subtype))
  conjugateTypes : ∀ {k G V : Type} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : Representation k G V),Representation.IsIrreducible rho →
    ∀ (H : Subgroup G) [H.Normal]
      (S T : Subrepresentation (rho.comp H.subtype)),
      Representation.IsIrreducible S.toRepresentation →
      Representation.IsIrreducible T.toRepresentation →
      ∃ g : G,Nonempty
        (Representation.Equiv
          (S.toRepresentation.comp (MulAut.conjNormal g).toMonoidHom) T.toRepresentation)

end SymmetricSubgroupAsymptotics.CliffordRawRestriction
