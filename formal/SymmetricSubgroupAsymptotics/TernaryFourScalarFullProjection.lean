import SymmetricSubgroupAsymptotics.TernaryFourScalarAugmentation
import SymmetricSubgroupAsymptotics.TernaryFourFullModuleCoordinates
import SymmetricSubgroupAsymptotics.CyclicKernelNormalGenerators

/-! The original scalar permutation action descends along the actual
projection from the full four-coordinate ternary module to augmentation.
Its kernel is the literal diagonal translation line. The scalar character
is retained on both source and target; no direct-product identification is
used for a nontrivial scalar character. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.TernaryFourScalarFullProjection

open TernaryFourAugmentationRepresentation SemidirectProduct
open TernaryA4SectionRegularEmbedding

abbrev FullVector := Fin 4 → ZMod 3
abbrev C3 := Multiplicative (ZMod 3)

def decodeLinear : FullVector →ₗ[ZMod 3] Vector where
  toFun := decode
  map_add' v w := by funext i; fin_cases i <;> rfl
  map_smul' a v := by funext i; fin_cases i <;> rfl

def projection : FullVector →ₗ[ZMod 3] Vector :=
  decodeLinear.comp augmentationProjection

theorem augmentationProjection_sum (v : FullVector) :
    ∑ i, augmentationProjection v i = 0 := by
  let z : ZMod 3 := ∑ i, v i
  have hpoint (i : Fin 4) : augmentationProjection v i = v i - z := rfl
  have hfour : ∀ a : ZMod 3, (4 : ℕ) • a = a := by decide +kernel
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  change z - (4 : ℕ) • z = 0
  rw [hfour z,sub_self]

theorem encode_projection (v : FullVector) :
    encode (projection v) = augmentationProjection v :=
  encode_decode _ (augmentationProjection_sum v)

theorem projection_encode (v : Vector) : projection (encode v) = v := by
  have hp : augmentationProjection (encode v) = encode v := by
    funext i
    change encode v i - ∑ j, encode v j = encode v i
    rw [encode_sum,sub_zero]
  change decode (augmentationProjection (encode v)) = v
  rw [hp,decode_encode]

theorem projection_eq_zero_iff (v : FullVector) :
    projection v = 0 ↔ ∀ i, v i = v 0 := by
  have he : projection v = 0 ↔ augmentationProjection v = 0 := by
    constructor
    · intro h
      rw [← encode_projection,h]
      exact map_zero encodeLinear
    · intro h
      apply encode_injective
      rw [encode_projection,h]
      exact (map_zero encodeLinear).symm
  rw [he]
  change v ∈ augmentationProjection.ker ↔ v ∈ TernaryA4InvariantSubmodules.diagonal
  rw [augmentationProjection_kernel]

variable {R : Type} [Group R]
variable (b : R →* Equiv.Perm (Fin 4)) (s : R →* (ZMod 3)ˣ)

abbrev Model := TernaryMonomialSemidirect.Model b s
abbrev Augmentation := TernaryFourScalarAugmentation.Model b s

theorem projection_equivariant (g : R) (v : FullVector) :
    projection (TernaryMonomialSemidirect.linearAction b s g v) =
      TernaryFourScalarAugmentation.linearHom b s g (projection v) := by
  have hfull : TernaryMonomialSemidirect.linearAction b s g v =
      (s g : ZMod 3) • TernaryA4InvariantSubmodules.coordinateAction (b g) v := by
    funext i
    change (s g : ZMod 3) * v (b g⁻¹ i) = (s g : ZMod 3) * v ((b g).symm i)
    rw [b.map_inv]
    rfl
  apply encode_injective
  rw [encode_projection,hfull,map_smul,augmentationProjection_equivariant,
    TernaryFourScalarAugmentation.encode_linearHom,encode_projection]
  rfl

def toAugmentation : Model b s →* Augmentation b s :=
  SemidirectProduct.map projection.toAddMonoidHom.toMultiplicative (MonoidHom.id R) (by
    intro g
    apply MonoidHom.ext
    intro v
    apply Multiplicative.toAdd.injective
    exact projection_equivariant b s g v.toAdd)

theorem toAugmentation_surjective : Function.Surjective (toAugmentation b s) := by
  intro g
  refine ⟨⟨Multiplicative.ofAdd (encode g.left.toAdd),g.right⟩,?_⟩
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    exact projection_encode g.left.toAdd
  · rfl

theorem kernel_right (g : (toAugmentation b s).ker) : g.1.right = 1 :=
  congrArg SemidirectProduct.right (MonoidHom.mem_ker.mp g.2)

theorem kernel_diagonal (g : (toAugmentation b s).ker) :
    ∀ i, g.1.left.toAdd i = g.1.left.toAdd 0 := by
  apply (projection_eq_zero_iff _).mp
  exact congrArg (fun q : Augmentation b s => q.left.toAdd)
    (MonoidHom.mem_ker.mp g.2)

def kernelValue : (toAugmentation b s).ker →* C3 where
  toFun g := Multiplicative.ofAdd (g.1.left.toAdd 0)
  map_one' := rfl
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    change g.1.left.toAdd 0 +
        (TernaryMonomialSemidirect.linearAction b s g.1.right h.1.left.toAdd) 0 =
      g.1.left.toAdd 0 + h.1.left.toAdd 0
    rw [kernel_right,map_one]
    rfl

theorem kernelValue_injective : Function.Injective (kernelValue b s) := by
  intro g h he
  apply Subtype.ext
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    calc
      g.1.left.toAdd i = g.1.left.toAdd 0 := kernel_diagonal b s g i
      _ = h.1.left.toAdd 0 := congrArg Multiplicative.toAdd he
      _ = h.1.left.toAdd i := (kernel_diagonal b s h i).symm
  · exact (kernel_right b s g).trans (kernel_right b s h).symm

instance kernel_isCyclic : IsCyclic (toAugmentation b s).ker :=
  isCyclic_of_injective (kernelValue b s) (kernelValue_injective b s)

theorem socle_two_of_augmentation_normal_total [Finite R]
    (hchain : ∀ A B : Subgroup (Augmentation b s),
      A.Normal → B.Normal → A ≤ B ∨ B ≤ A)
    {X : Type} [Group X] (rho : Model b s →* X) (hrho : Function.Surjective rho) :
    SocleNormalGeneratorBound X 2 :=
  CyclicSocleQuotientTools.socleBound_equiv
    (QuotientGroup.quotientKerEquivOfSurjective rho hrho)
    (quotientSocle_two_of_cyclic_kernel_normal_total
      (toAugmentation b s) (toAugmentation_surjective b s) hchain rho.ker)

end SymmetricSubgroupAsymptotics.TernaryFourScalarFullProjection

end
