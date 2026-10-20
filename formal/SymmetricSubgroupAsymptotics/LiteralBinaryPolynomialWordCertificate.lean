import SymmetricSubgroupAsymptotics.LiteralPolynomialSpanWitness

/-! A shared two-generator certificate for literal binary permutation modules.
The operator is a finite sum of actual acting words; the recurrence and
coordinate inverse are checked separately on the literal twelve coordinates. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators MonoidAlgebra
namespace SymmetricSubgroupAsymptotics
namespace LiteralBinaryPolynomialWordCertificate

def algebraElement {G : Type} [Group G] {s : ℕ} (words : Fin s → G) :
    (ZMod 2)[G] := ∑ j, Finsupp.single (words j) 1

theorem uniform_of_basis {G : Type} [Group G] {s h : ℕ}
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2))
    (words : Fin s → G) (T : Module.End (ZMod 2) (Fin 12 → ZMod 2))
    (C : LiteralPolynomialSpanWitness T 2 h)
    (hbasis : ∀ i x : Fin 12,
      (∑ j, rho (words j) (Pi.single i 1) x) = T (Pi.single i 1) x) :
    UniformSubrepresentationGeneratorBound rho 2 := by
  apply C.uniform rho (algebraElement words)
  symm
  apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
  intro i
  rw [Pi.basisFun_apply]
  funext x
  simpa [algebraElement, Representation.asAlgebraHom_single] using hbasis i x

end LiteralBinaryPolynomialWordCertificate
end SymmetricSubgroupAsymptotics
