import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Nat.Log

/-!
# Definitions for scalar-F4 heads

This lightweight module contains the data types shared by the scalar-F4
counting theorem and concrete finite target models.  Keeping the definitions
separate lets finite target verification avoid importing the full moment
proof.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- `F4` as a multiplicative group. -/
abbrev ScalarFour := Multiplicative (ZMod 2 × ZMod 2)

/-- Multiplication by a primitive cube root of unity. -/
def scalarFourOmegaAdd : ZMod 2 × ZMod 2 →+ ZMod 2 × ZMod 2 :=
  (AddMonoidHom.snd (ZMod 2) (ZMod 2)).prod
    (AddMonoidHom.fst (ZMod 2) (ZMod 2) + AddMonoidHom.snd (ZMod 2) (ZMod 2))

/-- Multiplication by `omega^c`. -/
def scalarFourTwistAdd (c : ZMod 3) : ZMod 2 × ZMod 2 →+ ZMod 2 × ZMod 2 :=
  if c = 0 then AddMonoidHom.id _
  else if c = 1 then scalarFourOmegaAdd
  else scalarFourOmegaAdd.comp scalarFourOmegaAdd

/-- Multiplication by `omega^c`, multiplicatively. -/
def scalarFourTwist (c : ZMod 3) : ScalarFour →* ScalarFour :=
  AddMonoidHom.toMultiplicative (scalarFourTwistAdd c)

/-- The first binary coordinate. -/
def scalarFourFst : ScalarFour →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative (AddMonoidHom.fst (ZMod 2) (ZMod 2))

/-- The cyclic target of an index-three top. -/
abbrev CyclicThree := Multiplicative (ZMod 3)

/-- An index-three quotient whose kernel carries a nonzero twisted `F4`
map: conjugation by `g` acts as `omega^theta(g)`. -/
structure ScalarFourHead (J : Type*) [Group J] where
  top : J →* CyclicThree
  top_surjective : Function.Surjective top
  map : top.ker →* ScalarFour
  twisted : ∀ (g : J) (f : top.ker),
    map (MulAut.conjNormal g f) =
      scalarFourTwist (Multiplicative.toAdd (top g)) (map f)
  map_ne_one : map ≠ 1

/-- A quotient `Q` with an index-three top whose kernel has a central binary
subgroup and scalar-F4 coordinates with that subgroup as joint kernel. -/
structure ScalarFourHeadedQuotient (Q : Type) [Group Q] where
  top : Q →* CyclicThree
  top_surjective : Function.Surjective top
  center : Subgroup top.ker
  center_comm : ∀ z ∈ center, ∀ p : top.ker, z * p = p * z
  center_twoGroup : IsPGroup 2 center
  layers : ℕ
  coord : Fin (layers + 1) → (top.ker →* ScalarFour)
  coord_center : ∀ j, ∀ z ∈ center, coord j z = 1
  coord_joint : ∀ p : top.ker, (∀ j, coord j p = 1) → p ∈ center
  coord_twisted : ∀ (q : Q) (p : top.ker) j,
    coord j (MulAut.conjNormal q p) =
      scalarFourTwist (Multiplicative.toAdd (top q)) (coord j p)
  coord_zero_surjective : Function.Surjective (coord 0)

namespace ScalarFourHeadedQuotient

variable {Q : Type} [Group Q] (h : ScalarFourHeadedQuotient Q)

/-- The binary exponent per unit of binary rank of an index-three kernel. -/
def weight : ℕ := (h.layers + 1) + Nat.log 2 (Nat.card h.center)

end ScalarFourHeadedQuotient

end SymmetricSubgroupAsymptotics

end
