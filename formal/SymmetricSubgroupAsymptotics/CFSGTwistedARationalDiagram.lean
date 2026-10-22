import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalReversal
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalRealization
import SymmetricSubgroupAsymptotics.CFSGSerreConcreteDiagrams

/-! Intertwining of the literal ORIGINAL rational Serre diagram map with
the explicit signed anti-diagonal Lie map. Equality is proved on all
original H/E/F generators, then through their actual free-Lie quotient.
It is not an assumed natural-model identification. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence

theorem rationalHom_ext_on_generators {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (f g : RationalLie A →ₗ⁅ℚ⁆ L)
    (h : ∀ k : CartanMatrix.Generators (Fin n), f (generator A k) = g (generator A k)) :
    f = g := by
  have hfree : f.comp (quotientMap A) = g.comp (quotientMap A) := by
    apply FreeLieAlgebra.hom_ext
    intro k
    simpa only [LieHom.comp_apply, quotientMap_of] using h k
  apply LieHom.ext
  intro x
  obtain ⟨y, rfl⟩ := quotientMap_surjective A x
  exact congrArg (fun F : Free (n := n) →ₗ⁅ℚ⁆ L => F y) hfree

theorem rationalNatural_diagram (r : ℕ) (x : RationalLie (CartanMatrix.A r)) :
    rationalNatural r
      (CFSGSerreDiagram.rationalMap (CartanMatrix.A r) Fin.revPerm
        (CFSGSerreDiagram.typeA_reverse_preserves r) x) =
      matrixDiagram ℚ r (rationalNatural r x) := by
  have he :
      (rationalNatural r).comp
        (CFSGSerreDiagram.rationalMap (CartanMatrix.A r) Fin.revPerm
          (CFSGSerreDiagram.typeA_reverse_preserves r)) =
      (matrixDiagram ℚ r).comp (rationalNatural r) := by
    apply rationalHom_ext_on_generators (CartanMatrix.A r)
    intro k
    cases k with
    | H i =>
      simp only [LieHom.comp_apply, CFSGSerreDiagram.rationalMap_generator,
        CFSGSerreDiagram.nodeRename, rationalNatural_H, matrixDiagram_cartan,
        Fin.revPerm_apply]
    | E i =>
      simp only [LieHom.comp_apply, CFSGSerreDiagram.rationalMap_generator,
        CFSGSerreDiagram.nodeRename, rationalNatural_E, matrixDiagram_positive,
        Fin.revPerm_apply]
    | F i =>
      simp only [LieHom.comp_apply, CFSGSerreDiagram.rationalMap_generator,
        CFSGSerreDiagram.nodeRename, rationalNatural_F, matrixDiagram_negative,
        Fin.revPerm_apply]
  exact congrArg (fun F : RationalLie (CartanMatrix.A r) →ₗ⁅ℚ⁆ Mat ℚ r => F x) he

theorem rationalNatural_diagramEquiv (r : ℕ) (x : RationalLie (CartanMatrix.A r)) :
    rationalNatural r
      (CFSGSerreDiagram.rationalEquiv (CartanMatrix.A r) Fin.revPerm
        (CFSGSerreDiagram.typeA_reverse_preserves r) x) =
      matrixDiagram ℚ r (rationalNatural r x) :=
  rationalNatural_diagram r x

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
