import SymmetricSubgroupAsymptotics.BinaryPermutationSemidirectNormalGenerators
import SymmetricSubgroupAsymptotics.TernaryMonomialCocycle

/-! The two actual binary sign coordinates act on labelled ternary
blocks. Their semidirect multiplication proves the coordinate cocycle;
the resulting ternary affine action is consequently a genuine group map.
A linear equivariant map on the sign coordinates permits the common-sign
image as well as the independent parity signs. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace TernaryParitySignModel

open BinaryPermutationSemidirectNormalGenerators (Vector)

def signInput (q : Vector →ₗ[ZMod 2] Vector) (j : Fin 2) :
    Multiplicative Vector →* Multiplicative (ZMod 2) where
  toFun w := Multiplicative.ofAdd (q w.toAdd j)
  map_one' := by
    apply Multiplicative.toAdd.injective
    change q 0 j = 0
    rw [map_zero]
    rfl
  map_mul' := by
    intro w z
    apply Multiplicative.toAdd.injective
    change q (w.toAdd + z.toAdd) j = q w.toAdd j + q z.toAdd j
    exact congrFun (q.map_add w.toAdd z.toAdd) j

def coefficient (q : Vector →ₗ[ZMod 2] Vector) (j : Fin 2) :
    Multiplicative Vector →* ZMod 3 :=
  (Units.coeHom (ZMod 3)).comp
    ((TernaryFourBlockMetacyclicModel.bitScalar true).comp (signInput q j))

variable {R X : Type} [Group R]
  (p : R →* Equiv.Perm (Fin 2)) (b : R →* Equiv.Perm X)
  (label : X → Fin 2)
  (hlabel : ∀ g i, label (b g i) = p g (label i))
  (q : Vector →ₗ[ZMod 2] Vector)
  (hq : ∀ g v,
    q (BinaryPermutationSemidirectNormalGenerators.linearAction p g v) =
      BinaryPermutationSemidirectNormalGenerators.linearAction p g (q v))

abbrev Complement := BinaryPermutationSemidirectNormalGenerators.Model p

def blockAction : Complement p →* Equiv.Perm X := b.comp SemidirectProduct.rightHom

def signs (g : Complement p) (i : X) : ZMod 3 := coefficient q (label i) g.left

include hq in
theorem coefficient_action (g : R) (w : Multiplicative Vector) (j : Fin 2) :
    coefficient q j
        (LinearSemidirectCoprimeSocleBounds.linearAction
          (BinaryPermutationSemidirectNormalGenerators.linearAction p) g w) =
      coefficient q (p g⁻¹ j) w := by
  exact congrArg
    (fun z : ZMod 2 ↦
      (TernaryFourBlockMetacyclicModel.bitScalar true (Multiplicative.ofAdd z) : ZMod 3))
    (congrFun (hq g w.toAdd) j)

theorem signs_one (i : X) : signs p label q 1 i = 1 :=
  (coefficient q (label i)).map_one

include hlabel hq in
theorem signs_mul (g h : Complement p) (i : X) :
    signs p label q (g * h) i =
      signs p label q g i * signs p label q h (blockAction p b g⁻¹ i) := by
  change coefficient q (label i)
      (g.left * LinearSemidirectCoprimeSocleBounds.linearAction
        (BinaryPermutationSemidirectNormalGenerators.linearAction p) g.right h.left) =
    coefficient q (label i) g.left * coefficient q (label (b g.right⁻¹ i)) h.left
  rw [map_mul, coefficient_action p q hq, hlabel]

def linearAction : Complement p →* ((X → ZMod 3) ≃ₗ[ZMod 3] (X → ZMod 3)) :=
  TernaryMonomialCocycle.linearAction (blockAction p b) (signs p label q)
    (signs_one p label q) (signs_mul p b label hlabel q hq)

abbrev Model := LinearSemidirectCoprimeSocleBounds.Model
  (linearAction p b label hlabel q hq)

def action : Model p b label hlabel q hq →* Equiv.Perm (X × ZMod 3) :=
  TernaryMonomialCocycle.action (blockAction p b) (signs p label q)
    (signs_one p label q) (signs_mul p b label hlabel q hq)

theorem linearAction_inr (g : R) (v : X → ZMod 3) (i : X) :
    linearAction p b label hlabel q hq (SemidirectProduct.inr g) v i = v (b g⁻¹ i) := by
  change coefficient q (label i) 1 * v (b g⁻¹ i) = v (b g⁻¹ i)
  rw [map_one, one_mul]

end TernaryParitySignModel
end SymmetricSubgroupAsymptotics

end
