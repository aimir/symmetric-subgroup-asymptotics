import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedDiagonalCardinality
import Mathlib.Algebra.CharP.Two

/-! The actual two-unit Ree torus as a group homomorphism. Squaring
on its middle parameter is onto, including at the Tits field size. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorusGroup
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedTorus CFSGReeFFourParameterizedTorusCovariance
open CFSGFFourOriginalProductTorus

def fixedTorusTupleHom (m : ℕ) :
    ((Field m)ˣ × (Field m)ˣ) →* (Fin 4 → (Field m)ˣ) where
  toFun p := fixedTorusTuple m p.1 p.2
  map_one' := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · change unitPower m 1 1 = 1
      exact map_one _
    · change unitPower m 0 1 = 1
      exact map_one _
  map_mul' p q := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · change unitPower m 1 (p.2*q.2) = unitPower m 1 p.2 * unitPower m 1 q.2
      exact map_mul _ _ _
    · change unitPower m 0 (p.1*q.1) = unitPower m 0 p.1 * unitPower m 0 q.1
      exact map_mul _ _ _

def fixedTorusHom (m : ℕ) : ((Field m)ˣ × (Field m)ˣ) →* originalModelFixed m where
  toFun p := fixedTorus m p.1 p.2
  map_one' := by
    apply Subtype.ext
    change modelProductTorusHom (Field m) (fixedTorusTupleHom m 1) = 1
    rw [map_one, map_one]
  map_mul' p q := by
    apply Subtype.ext
    change modelProductTorusHom (Field m) (fixedTorusTupleHom m (p*q)) =
      modelProductTorusHom (Field m) (fixedTorusTupleHom m p) *
        modelProductTorusHom (Field m) (fixedTorusTupleHom m q)
    rw [map_mul, map_mul]

def middleTorusHom (m : ℕ) : (Field m)ˣ →* originalModelFixed m :=
  (fixedTorusHom m).comp
    ((1 : (Field m)ˣ →* (Field m)ˣ).prod (MonoidHom.id (Field m)ˣ))

theorem middleTorusHom_apply (m : ℕ) (b : (Field m)ˣ) :
    middleTorusHom m b = fixedTorus m 1 b := rfl

theorem unit_square_surjective (m : ℕ) :
    Function.Surjective (fun a : (Field m)ˣ => a^2) := by
  apply Finite.surjective_of_injective
  intro a b h
  apply Units.ext
  apply CharTwo.sq_injective
  exact congrArg (fun x : (Field m)ˣ => (x : Field m)) h

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorusGroup
