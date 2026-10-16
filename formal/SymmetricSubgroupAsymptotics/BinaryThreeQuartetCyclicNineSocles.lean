import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow207Socles
import SymmetricSubgroupAsymptotics.LinearSemidirectSubgroupSocles

/-! The actual order-nine linear image on three binary planes.
Its odd cyclic action has one uniform module generator. Coprime maximum
sharing therefore gives one socle generator on every original quotient
of every actual affine subgroup with this full projection. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryThreeQuartetCyclicNineSocles
open LinearSemidirectCoprimeSocleBounds LinearSemidirectSubgroupKernelChart
open PrimitiveAffineDegreeTwoTwelveRow207Socles (Odd Vector)
open BinaryPlanePermutationAffineEquiv (Plane)

def linear : Odd →* (Vector ≃ₗ[ZMod 2] Vector) :=
  PrimitiveAffineDegreeTwoTwelveRow207Socles.rho.comp
    PrimitiveAffineDegreeTwoTwelveRow207Socles.oddMap

theorem uniform : UniformSubrepresentationGeneratorBound (linearRepresentation linear) 1 := by
  have hcard : Nat.card Odd = 9 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  letI : NeZero (Nat.card Odd : ZMod 2) := ⟨by rw [hcard]; decide⟩
  apply FunctionBlockLocalGeneratorUniform.uniform_of_restriction
    (linearRepresentation linear) (0 : Fin 3) (![1, 0] : Plane)
    (Pi.basisFun (ZMod 2) (Fin 2)) (MonoidHom.id Odd)
  · intro j
    refine ⟨Multiplicative.ofAdd (6 * j.val : ZMod 9), ?_⟩
    rw [Pi.basisFun_apply]
    funext i t
    revert j i t
    decide +kernel
  · intro i
    let n : Fin 3 := ![0, 2, 1] i
    refine ⟨Multiplicative.ofAdd (n.val : ZMod 9),
      (PrimitiveAffineDegreeTwoTwelveRow207Socles.linearImage
        (DihedralGroup.r (n.val : ZMod 9))).left i, ?_⟩
    intro v
    funext j t
    revert i v j t
    decide +kernel

abbrev Model := LinearSemidirectCoprimeSocleBounds.Model linear

def toDihedralAffine : Model →* PrimitiveAffineDegreeTwoTwelveRow207Socles.Affine where
  toFun g := ⟨g.left, PrimitiveAffineDegreeTwoTwelveRow207Socles.oddMap g.right⟩
  map_one' := by
    apply SemidirectProduct.ext
    · rfl
    · exact map_one _
  map_mul' g h := by
    apply SemidirectProduct.ext
    · rfl
    · exact map_mul _ _ _

def action : Model →* Equiv.Perm (Fin 12) :=
  PrimitiveAffineDegreeTwoTwelveRow207Socles.action.comp toDihedralAffine

def literalAction (e : Fin 12 ≃ Fin 12) : Model →* Equiv.Perm (Fin 12) :=
  e.permCongrHom.toMonoidHom.comp action

theorem actual_socle_of_surjective (K : Subgroup Model)
    (hsurj : Function.Surjective (projection linear K))
    {Q : Type} [Group Q] (pi : K →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q 1 := by
  have hincl : Function.Surjective (Image linear K).subtype := by
    intro c
    obtain ⟨k, hk⟩ := hsurj c
    exact ⟨⟨c, ⟨k, hk⟩⟩, rfl⟩
  have hu : UniformSubrepresentationGeneratorBound (imageRepresentation linear K) 1 :=
    UniformSubrepresentationGeneratorBound.comp_of_surjective
      (linearRepresentation linear) (Image linear K).subtype hincl uniform
  let identityMap : Representation.IntertwiningMap
      (imageRepresentation linear K) (imageRepresentation linear K) :=
    { toLinearMap := LinearMap.id, isIntertwining' _ := rfl }
  have hg : RepresentationGeneratedBy (imageRepresentation linear K) 1 :=
    representationGeneratedBy_of_injective_of_uniform hu identityMap (fun _ _ h => h)
  have hc : Nat.card Odd = 9 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hcop : Nat.Coprime 2 (Nat.card (Image linear K)) :=
    (show Nat.Coprime 2 (Nat.card Odd) by rw [hc]; decide).of_dvd_right
      (Image linear K).card_subgroup_dvd_card
  apply LinearSemidirectSubgroupSocles.coprime_socle_of_surjective linear K hcop 1 1 hg ?_ pi hpi
  intro H hH
  letI := hH
  exact CoprimeCyclicQuotientSocles.normalGen_le_one_of_isCyclic H

theorem quotientSocle {n : ℕ} (e : Fin 12 ≃ Fin 12)
    (lifted : Fin n → Model) (target : Fin n → Equiv.Perm (Fin 12))
    (hbinding : ∀ i, literalAction e (lifted i) = target i)
    (j : Fin n) (hj : (lifted j).right = Multiplicative.ofAdd (1 : ZMod 9))
    (N : Subgroup (Subgroup.closure (Set.range target))) [N.Normal] :
    SocleNormalGeneratorBound (Subgroup.closure (Set.range target) ⧸ N) 1 := by
  let K := Subgroup.closure (Set.range lifted)
  have hsurj : Function.Surjective (projection linear K) := by
    intro c
    have hp : ∃ m : Fin 9, (Multiplicative.ofAdd (1 : ZMod 9)) ^ m.val = c := by
      revert c
      decide +kernel
    obtain ⟨m, hm⟩ := hp
    refine ⟨closureGenerators lifted j ^ m.val, ?_⟩
    rw [map_pow]
    change (lifted j).right ^ m.val = c
    rw [hj, hm]
  let f : K →* Equiv.Perm (Fin 12) := (literalAction e).comp K.subtype
  let q := GeneratedLiteralImage.toTop f (closureGenerators lifted) target (Equiv.refl _)
    (closureGenerators_full lifted) hbinding
  have hq : Function.Surjective q := GeneratedLiteralImage.toTop_surjective
    f (closureGenerators lifted) target (Equiv.refl _) (closureGenerators_full lifted) hbinding
  exact actual_socle_of_surjective K hsurj ((QuotientGroup.mk' N).comp q)
    ((QuotientGroup.mk'_surjective N).comp hq)

end SymmetricSubgroupAsymptotics.BinaryThreeQuartetCyclicNineSocles

end
