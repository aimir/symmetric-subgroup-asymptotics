import SymmetricSubgroupAsymptotics.ActualBlockWreathEmbedding
import SymmetricSubgroupAsymptotics.BinaryPlaneOddKernelMultiplicityUniform

/-! Every actual four-point block action has its faithful literal affine
wreath coordinates. The linear image is the actual image, not a supplied
split complement. No primitive-group or field-recognition premise is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FourPointBlockAffineCoordinates
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open PermutationalWreathProduct

variable {G Ω X : Type} [Group G] [Finite G] [Finite Ω] [Finite X]
    [MulAction G Ω] [MulAction G X] [MulAction.IsPretransitive G X]
    [FaithfulSMul G Ω]
    (b : Ω → X) (hb : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω)
    (x₀ : X) (hfour : Nat.card (originalBlockFibre b x₀) = 4)

abbrev Top := ActualBlockWreathEmbedding.Top (A := G) (X := X)
abbrev Component := ActualBlockWreathEmbedding.Component b hb x₀
abbrev Affine := BinaryPlaneWreathNormalGenerators.Model (R := Top (G := G) (X := X)) (I := X)
abbrev LinearFrame := W (R := Top (G := G) (X := X)) (I := X)

/-- Relabel the literal base fibre by its four binary-plane points. -/
def fibreChart : originalBlockFibre b x₀ ≃ Plane :=
  (Finite.equivFinOfCardEq hfour).trans
    (Finite.equivFinOfCardEq (show Nat.card Plane = 4 by
      simp [Plane])).symm

def localAffine : Component b hb x₀ →* BinaryPlanePermutationAffineEquiv.Model :=
  affineMap.comp ((fibreChart b x₀ hfour).permCongrHom.toMonoidHom.comp
    (Component b hb x₀).subtype)

omit [Finite G] [Finite X] [MulAction.IsPretransitive G X] [FaithfulSMul G Ω] in
theorem localAffine_injective : Function.Injective (localAffine b hb x₀ hfour) :=
  affineMap_injective.comp ((fibreChart b x₀ hfour).permCongrHom.injective.comp
    Subtype.val_injective)

/-- The whole original group embeds in the actual binary-plane affine frame. -/
def affineEmbedding : G →* Affine (G := G) (X := X) :=
  (PermutationalWreathAffineCoordinates.equiv
    (R := Top (G := G) (X := X)) (I := X) localAction).symm.toMonoidHom.comp
      ((mapBase (Q := Top (G := G) (X := X)) (I := X)
        (localAffine b hb x₀ hfour)).comp (ActualBlockWreathEmbedding.embedding b hb x₀))

theorem affineEmbedding_injective : Function.Injective (affineEmbedding b hb x₀ hfour) := by
  intro g h he
  apply ActualBlockWreathEmbedding.embedding_injective b hb x₀
  have hw := (PermutationalWreathAffineCoordinates.equiv
    (R := Top (G := G) (X := X)) (I := X) localAction).symm.injective he
  apply PermutationalWreathProduct.ext
  · funext i
    exact localAffine_injective b hb x₀ hfour
      (congrArg (fun z : PermutationalWreathProduct BinaryPlanePermutationAffineEquiv.Model
        (Top (G := G) (X := X)) X => z.left i) hw)
  · exact congrArg (fun z : PermutationalWreathProduct BinaryPlanePermutationAffineEquiv.Model
      (Top (G := G) (X := X)) X => z.right) hw

def linearMap : G →* LinearFrame (G := G) (X := X) :=
  (SemidirectProduct.rightHom : Affine (G := G) (X := X) →* _).comp
    (affineEmbedding b hb x₀ hfour)

abbrev linearImage : Subgroup (LinearFrame (G := G) (X := X)) :=
  (linearMap b hb x₀ hfour).range

def projection : G →* linearImage b hb x₀ hfour :=
  (linearMap b hb x₀ hfour).rangeRestrict

omit [Finite G] [Finite X] in
theorem projection_surjective : Function.Surjective (projection b hb x₀ hfour) :=
  (linearMap b hb x₀ hfour).rangeRestrict_surjective

/-- The original action on blocks is retained without changing its carrier. -/
theorem linearMap_right (g : G) :
    (linearMap b hb x₀ hfour g).right =
      (ActualBlockWreathEmbedding.topMap (A := G) (X := X)).rangeRestrict g := by
  let e := PermutationalWreathAffineCoordinates.equiv
    (R := Top (G := G) (X := X)) (I := X) localAction
  let w := mapBase (Q := Top (G := G) (X := X)) (I := X)
    (localAffine b hb x₀ hfour) (ActualBlockWreathEmbedding.embedding b hb x₀ g)
  exact congrArg (fun z : PermutationalWreathProduct BinaryPlanePermutationAffineEquiv.Model
    (Top (G := G) (X := X)) X => z.right) (e.apply_symm_apply w)

/-- Original transitivity supplies actual transporters in the linear image. -/
theorem image_transitive (i j : X) : ∃ h : linearImage b hb x₀ hfour,
    (h : LinearFrame (G := G) (X := X)).right • i = j := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G i j
  refine ⟨projection b hb x₀ hfour g,?_⟩
  change (linearMap b hb x₀ hfour g).right • i = j
  rw [linearMap_right]
  exact hg

end SymmetricSubgroupAsymptotics.FourPointBlockAffineCoordinates
