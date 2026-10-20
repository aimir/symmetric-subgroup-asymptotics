import SymmetricSubgroupAsymptotics.BinaryThreeQuartetLiteralSocles
import SymmetricSubgroupAsymptotics.FunctionBlockLocalGeneratorUniform
import SymmetricSubgroupAsymptotics.LinearSemidirectSubgroupSocles
import SymmetricSubgroupAsymptotics.CyclicByCyclicNormalGenerators

/-! A scalar Singer commuting with a three-block rotation supplies one
uniform generator on the actual six-dimensional binary module. For every
actual affine subgroup with full C3 x C3 image, coprime maximum sharing
bounds all original quotient socles by two. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryThreeQuartetCubicSquareSocles
open SemidirectProduct BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open LinearSemidirectCoprimeSocleBounds LinearSemidirectSubgroupKernelChart

abbrev Cubic := Multiplicative (ZMod 3)
abbrev R := Cubic × Cubic
abbrev Vector := Fin 3 → Plane
abbrev Lin := W (R := Equiv.Perm (Fin 3)) (I := Fin 3)

def cycle : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

def linearImage : R →* Lin where
  toFun c := ⟨fun _ => singer ^ (Multiplicative.toAdd c.1).val,
    cycle ^ (Multiplicative.toAdd c.2).val⟩
  map_one' := by
    apply PermutationalWreathProduct.ext
    · funext i; apply LinearEquiv.ext; intro v
      revert i v; decide +kernel
    · apply Equiv.ext; intro i; revert i; decide +kernel
  map_mul' c d := by
    apply PermutationalWreathProduct.ext
    · funext i; apply LinearEquiv.ext; intro v
      revert c d i v; decide +kernel
    · apply Equiv.ext; intro i; revert c d i; decide +kernel

def rho : R →* (Vector ≃ₗ[ZMod 2] Vector) where
  toFun c := {
    toFun v := fun i => (linearImage c).left i (v ((linearImage c).right⁻¹ i))
    invFun v := fun i => ((linearImage c).left ((linearImage c).right i)).symm
      (v ((linearImage c).right i))
    left_inv := by intro v; funext i; simp
    right_inv := by intro v; funext i; simp
    map_add' := by intro v w; funext i; exact map_add _ _ _
    map_smul' := by
      intro a v
      funext i
      exact map_smul ((linearImage c).left i) a (v ((linearImage c).right⁻¹ i)) }
  map_one' := by
    apply LinearEquiv.ext; intro v; funext i
    change (linearImage 1).left i (v ((linearImage 1).right⁻¹ i)) = v i
    rw [map_one]; rfl
  map_mul' c d := by
    apply LinearEquiv.ext; intro v; funext i
    change (linearImage (c*d)).left i (v ((linearImage (c*d)).right⁻¹ i)) = _
    rw [map_mul]; rfl

theorem uniform : UniformSubrepresentationGeneratorBound (linearRepresentation rho) 1 := by
  have hc : Nat.card Cubic = 3 := by
    rw [Nat.card_congr Multiplicative.toAdd,Nat.card_zmod]
  letI : NeZero (Nat.card R : ZMod 2) := ⟨by rw [Nat.card_prod,hc]; decide⟩
  apply FunctionBlockLocalGeneratorUniform.uniform_of_restriction
    (linearRepresentation rho) (0 : Fin 3) (![1,0] : Plane)
    (Pi.basisFun (ZMod 2) (Fin 2)) (MonoidHom.id R)
  · intro j
    refine ⟨(Multiplicative.ofAdd (j.val : ZMod 3),1),?_⟩
    rw [Pi.basisFun_apply]
    funext i t
    revert j i t; decide +kernel
  · intro i
    refine ⟨(1,Multiplicative.ofAdd (i.val : ZMod 3)),LinearEquiv.refl _ _,?_⟩
    intro v; funext j t
    revert i v j t; decide +kernel

abbrev Model := LinearSemidirectCoprimeSocleBounds.Model rho

def toWreath : Model →* BinaryThreeQuartetLiteralSocles.Model (R := Equiv.Perm (Fin 3)) where
  toFun g := ⟨fun i => Multiplicative.ofAdd (g.left.toAdd i),linearImage g.right⟩
  map_one' := by
    apply SemidirectProduct.ext
    · rfl
    · exact linearImage.map_one
  map_mul' g h := by
    apply SemidirectProduct.ext
    · rfl
    · exact linearImage.map_mul _ _

def action : Model →* Equiv.Perm (Fin 12) :=
  BinaryThreeQuartetLiteralSocles.action.comp toWreath

def literalAction (e : Fin 12 ≃ Fin 12) : Model →* Equiv.Perm (Fin 12) :=
  e.permCongrHom.toMonoidHom.comp action

theorem actual_socle_of_surjective (K : Subgroup Model)
    (hsurj : Function.Surjective (projection rho K))
    {Q : Type} [Group Q] (pi : K →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q 2 := by
  have hincl : Function.Surjective (Image rho K).subtype := by
    intro c; obtain ⟨k,hk⟩ := hsurj c
    exact ⟨⟨c,⟨k,hk⟩⟩,rfl⟩
  have hu : UniformSubrepresentationGeneratorBound (imageRepresentation rho K) 1 :=
    UniformSubrepresentationGeneratorBound.comp_of_surjective
      (linearRepresentation rho) (Image rho K).subtype hincl uniform
  let idMap : Representation.IntertwiningMap
      (imageRepresentation rho K) (imageRepresentation rho K) :=
    { toLinearMap := LinearMap.id,isIntertwining' _ := rfl }
  have hg : RepresentationGeneratedBy (imageRepresentation rho K) 1 :=
    representationGeneratedBy_of_injective_of_uniform hu idMap (fun _ _ h => h)
  have hc : Nat.card Cubic = 3 := by
    rw [Nat.card_congr Multiplicative.toAdd,Nat.card_zmod]
  have hcop : Nat.Coprime 2 (Nat.card (Image rho K)) :=
    (show Nat.Coprime 2 (Nat.card R) by rw [Nat.card_prod,hc]; decide).of_dvd_right
      (Image rho K).card_subgroup_dvd_card
  apply LinearSemidirectSubgroupSocles.coprime_socle_of_surjective rho K hcop 1 2 hg ?_ pi hpi
  intro H hH
  letI := hH
  let E := (MonoidHom.snd Cubic Cubic).ker
  letI : IsCyclic E := by
    exact isCyclic_of_injective
      ((MonoidHom.fst Cubic Cubic).comp E.subtype) (by
        intro x y h
        apply Subtype.ext
        apply Prod.ext h
        have hx : x.val.2 = 1 := x.property
        have hy : y.val.2 = 1 := y.property
        exact hx.trans hy.symm)
  let e : R ⧸ E ≃* Cubic :=
    QuotientGroup.quotientKerEquivOfSurjective (MonoidHom.snd Cubic Cubic)
      (fun x => ⟨(1,x),rfl⟩)
  letI : IsCyclic (R ⧸ E) := isCyclic_of_injective e.toMonoidHom e.injective
  have hR : ∀ L : Subgroup R, L.Normal → MarkedC4.normalGen L ≤ 2 := by
    intro L hL; letI := hL
    exact CyclicByCyclicNormalGenerators.normalGen_le_two E L
  let eImage : Image rho K ≃* R := MulEquiv.ofBijective (Image rho K).subtype
    ⟨Subtype.val_injective,hincl⟩
  exact CoprimeKernelQuotientSocles.normalGen_image_bound
    eImage.symm.toMonoidHom eImage.symm.surjective 2 hR H

theorem quotientSocle {n : ℕ} (e : Fin 12 ≃ Fin 12)
    (lifted : Fin n → Model) (target : Fin n → Equiv.Perm (Fin 12))
    (hbinding : ∀ i,literalAction e (lifted i) = target i)
    (j k : Fin n)
    (hj : (lifted j).right = (Multiplicative.ofAdd 1,1))
    (hk : (lifted k).right = (1,Multiplicative.ofAdd 1))
    (N : Subgroup (Subgroup.closure (Set.range target))) [N.Normal] :
    SocleNormalGeneratorBound (Subgroup.closure (Set.range target) ⧸ N) 2 := by
  let K := Subgroup.closure (Set.range lifted)
  have hsurj : Function.Surjective (projection rho K) := by
    intro c
    have hp : ∃ m q : Fin 3,
        (Multiplicative.ofAdd (1 : ZMod 3))^m.val = c.1 ∧
        (Multiplicative.ofAdd (1 : ZMod 3))^q.val = c.2 := by
      revert c; decide +kernel
    obtain ⟨m,q,hm,hq⟩ := hp
    refine ⟨closureGenerators lifted j ^ m.val * closureGenerators lifted k ^ q.val,?_⟩
    rw [map_mul,map_pow,map_pow]
    change (lifted j).right^m.val * (lifted k).right^q.val = c
    rw [hj,hk]
    apply Prod.ext
    · simpa using hm
    · simpa using hq
  let f : K →* Equiv.Perm (Fin 12) := (literalAction e).comp K.subtype
  let q := GeneratedLiteralImage.toTop f (closureGenerators lifted) target (Equiv.refl _)
    (closureGenerators_full lifted) hbinding
  have hq : Function.Surjective q := GeneratedLiteralImage.toTop_surjective
    f (closureGenerators lifted) target (Equiv.refl _) (closureGenerators_full lifted) hbinding
  exact actual_socle_of_surjective K hsurj ((QuotientGroup.mk' N).comp q)
    ((QuotientGroup.mk'_surjective N).comp hq)

end SymmetricSubgroupAsymptotics.BinaryThreeQuartetCubicSquareSocles
end
