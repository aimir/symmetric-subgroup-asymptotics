import SymmetricSubgroupAsymptotics.BinaryPlaneWreathNormalGenerators

/-! Explicit affine coordinates and literal point action for a wreath
of permutations of the four binary-plane points. All maps are given by
coordinate formulas, so original generator bindings remain small point
identities rather than abstract equivalence computations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlanePermutationWreathCoordinates

open SemidirectProduct BinaryPlanePermutationAffineEquiv

variable {R I : Type} [Group R] [MulAction R I]

abbrev W := PermutationalWreathProduct (Equiv.Perm Plane) R I
abbrev Model := PermutationalWreathAffineCoordinates.Model (R := R) (I := I)
  BinaryPlaneWreathIrreducible.localAction

def coordinates : W (R := R) (I := I) →* Model (R := R) (I := I) where
  toFun g := ⟨fun i => Multiplicative.ofAdd (g.left i 0),
    ⟨fun i => linearPart (g.left i),g.right⟩⟩
  map_one' := by
    apply SemidirectProduct.ext
    · rfl
    · apply PermutationalWreathProduct.ext
      · funext i; exact linearPart.map_one
      · rfl
  map_mul' g h := by
    apply SemidirectProduct.ext
    · funext i
      exact congrArg SemidirectProduct.left
        (affineMap.map_mul (g.left i) (h.left (g.right⁻¹ • i)))
    · apply PermutationalWreathProduct.ext
      · funext i; exact linearPart.map_mul _ _
      · rfl

def localPointAction : BinaryPlanePermutationAffineEquiv.Model →* Equiv.Perm Plane where
  toFun := permutation
  map_one' := by
    apply Equiv.ext
    intro v
    change 0+v=v
    exact zero_add v
  map_mul' g h := by
    apply Equiv.ext
    intro v
    change (g.left.toAdd + g.right h.left.toAdd) + g.right (h.right v) =
      g.left.toAdd + g.right (h.left.toAdd+h.right v)
    rw [map_add,add_assoc]

def pointWreath : Model (R := R) (I := I) →* W (R := R) (I := I) where
  toFun g := ⟨fun i => localPointAction ⟨g.left i,g.right.left i⟩,g.right.right⟩
  map_one' := by
    apply PermutationalWreathProduct.ext
    · funext i; exact localPointAction.map_one
    · rfl
  map_mul' g h := by
    apply PermutationalWreathProduct.ext
    · funext i
      exact localPointAction.map_mul ⟨g.left i,g.right.left i⟩
        ⟨h.left (g.right.right⁻¹ • i),h.right.left (g.right.right⁻¹ • i)⟩
    · rfl

theorem pointWreath_coordinates (w : W (R := R) (I := I)) :
    pointWreath (coordinates w) = w := by
  apply PermutationalWreathProduct.ext
  · funext i
    apply affineMap_injective
    exact affineMap_permutation (affineMap (w.left i))
  · rfl

def pointAction : Model (R := R) (I := I) →* Equiv.Perm (Plane × I) :=
  PermutationalWreathProduct.toPerm.comp pointWreath

@[simp] theorem pointAction_apply (g : Model (R := R) (I := I)) (p : Plane × I) :
    pointAction g p =
      ((g.left (g.right.right • p.2)).toAdd + g.right.left (g.right.right • p.2) p.1,
        g.right.right • p.2) := rfl

theorem pointAction_coordinates (w : W (R := R) (I := I)) :
    pointAction (coordinates w) = PermutationalWreathProduct.toPerm w := by
  change PermutationalWreathProduct.toPerm (pointWreath (coordinates w)) = _
  rw [pointWreath_coordinates]

instance [Finite R] [Finite I] : Finite (Model (R := R) (I := I)) := by
  letI : Fintype I := Fintype.ofFinite I
  letI : DecidableEq I := Classical.decEq I
  exact Finite.of_equiv _ SemidirectProduct.equivProd.symm

end SymmetricSubgroupAsymptotics.BinaryPlanePermutationWreathCoordinates

end
