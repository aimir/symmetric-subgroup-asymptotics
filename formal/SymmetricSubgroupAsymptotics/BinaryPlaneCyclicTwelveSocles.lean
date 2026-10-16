import SymmetricSubgroupAsymptotics.BinaryThreeQuartetLiteralSocles
import SymmetricSubgroupAsymptotics.FunctionBlockLocalGeneratorUniform
import SymmetricSubgroupAsymptotics.LinearSemidirectSubgroupSocles

/-! A binary plane with a cyclic twelve complement. Restriction to its
order-three subgroup proves a uniform one-generator module bound; the
actual cyclic image contributes one further normal generator. Every
original normal quotient consequently has socle bound two. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneCyclicTwelveSocles
open SemidirectProduct BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open LinearSemidirectCoprimeSocleBounds LinearSemidirectSubgroupKernelChart
abbrev R := Multiplicative (ZMod 12)
abbrev Cubic := Multiplicative (ZMod 3)
abbrev Vector := Fin 1 → Plane

def linear : R →* (Vector ≃ₗ[ZMod 2] Vector) where
  toFun c := {
    toFun v := fun i => (singer ^ (Multiplicative.toAdd c).val) (v i)
    invFun v := fun i => (singer ^ (Multiplicative.toAdd c).val).symm (v i)
    left_inv := by intro v; funext i; simp
    right_inv := by intro v; funext i; simp
    map_add' := by intro v w; funext i; exact map_add _ _ _
    map_smul' := by
      intro a v
      funext i
      exact map_smul (singer ^ (Multiplicative.toAdd c).val) a (v i) }
  map_one' := by
    apply LinearEquiv.ext; intro v; funext i t
    revert v i t; decide +kernel
  map_mul' c d := by
    apply LinearEquiv.ext; intro v; funext i t
    revert c d v i t; decide +kernel

def cubicMap : Cubic →* R where
  toFun c := Multiplicative.ofAdd (4 * (Multiplicative.toAdd c).val : ZMod 12)
  map_one' := rfl
  map_mul' c d := by revert c d; decide +kernel

theorem uniform : UniformSubrepresentationGeneratorBound (linearRepresentation linear) 1 := by
  have hc : Nat.card Cubic = 3 := by
    rw [Nat.card_congr Multiplicative.toAdd,Nat.card_zmod]
  letI : NeZero (Nat.card Cubic : ZMod 2) := ⟨by rw [hc]; decide⟩
  apply FunctionBlockLocalGeneratorUniform.uniform_of_restriction
    (linearRepresentation linear) (0 : Fin 1) (![1,0] : Plane)
    (Pi.basisFun (ZMod 2) (Fin 2)) cubicMap
  · intro j
    refine ⟨Multiplicative.ofAdd (j.val : ZMod 3),?_⟩
    rw [Pi.basisFun_apply]
    funext i t; revert j i t; decide +kernel
  · intro i
    refine ⟨1,LinearEquiv.refl _ _,?_⟩
    intro v; funext j t; revert i v j t; decide +kernel

abbrev Model := LinearSemidirectCoprimeSocleBounds.Model linear

def cycle : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3

def blockImage : R →* Equiv.Perm (Fin 4) where
  toFun c := cycle ^ (Multiplicative.toAdd c).val
  map_one' := rfl
  map_mul' c d := by apply Equiv.ext; intro i; revert c d i; decide +kernel

def toWreath : Model →*
    BinaryPlanePermutationWreathCoordinates.Model (R := Equiv.Perm (Fin 4)) (I := Fin 4) where
  toFun g := ⟨fun _ => Multiplicative.ofAdd (g.left.toAdd 0),
    ⟨fun _ => singer ^ (Multiplicative.toAdd g.right).val,blockImage g.right⟩⟩
  map_one' := by
    apply SemidirectProduct.ext
    · rfl
    · apply PermutationalWreathProduct.ext
      · funext i; apply LinearEquiv.ext; intro v; revert i v; decide +kernel
      · exact blockImage.map_one
  map_mul' g h := by
    apply SemidirectProduct.ext
    · rfl
    · apply PermutationalWreathProduct.ext
      · funext i; apply LinearEquiv.ext; intro v
        have hm := congrArg (fun L : Vector ≃ₗ[ZMod 2] Vector => L (fun _ => v) 0)
          (linear.map_mul g.right h.right)
        exact hm
      · exact blockImage.map_mul _ _

def pointChart : Plane × Fin 4 ≃ Fin 16 :=
  (Equiv.prodCongr BinaryThreeQuartetLiteralSocles.planeLabel (Equiv.refl (Fin 4))).trans
    finProdFinEquiv

def action : Model →* Equiv.Perm (Fin 16) :=
  pointChart.permCongrHom.toMonoidHom.comp
    (BinaryPlanePermutationWreathCoordinates.pointAction.comp toWreath)

def literalAction (e : Fin 16 ≃ Fin 16) : Model →* Equiv.Perm (Fin 16) :=
  e.permCongrHom.toMonoidHom.comp action

theorem actual_socle_of_surjective (K : Subgroup Model)
    (hsurj : Function.Surjective (projection linear K))
    {Q : Type} [Group Q] (pi : K →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q 2 := by
  letI : Finite Q := Finite.of_surjective pi hpi
  have hincl : Function.Surjective (Image linear K).subtype := by
    intro c; obtain ⟨k,hk⟩ := hsurj c
    exact ⟨⟨c,⟨k,hk⟩⟩,rfl⟩
  have hu : UniformSubrepresentationGeneratorBound (imageRepresentation linear K) 1 :=
    UniformSubrepresentationGeneratorBound.comp_of_surjective
      (linearRepresentation linear) (Image linear K).subtype hincl uniform
  have hgen : ∀ H : Subgroup K, H.Normal → MarkedC4.normalGen H ≤ 2 := by
    intro H hH; letI := hH
    apply LinearSemidirectSubgroupSocles.normalGen_le linear K 1 1 hu ?_ H
    intro L hL; letI := hL
    exact CoprimeCyclicQuotientSocles.normalGen_le_one_of_isCyclic L
  have htuples : ∀ H : Subgroup K, H.Normal →
      ∃ x : Fin 2 → K, Subgroup.normalClosure (Set.range x) = H := by
    intro H hH
    letI := hH
    exact exists_normal_generating_tuple_of_normalGen_le H (hgen H hH)
  exact normal_generating_tuples_of_surjective pi hpi htuples
    (finiteGroupSocle Q) inferInstance

theorem quotientSocle {n : ℕ} (e : Fin 16 ≃ Fin 16)
    (lifted : Fin n → Model) (target : Fin n → Equiv.Perm (Fin 16))
    (hbinding : ∀ i,literalAction e (lifted i) = target i)
    (j : Fin n) (hj : (lifted j).right = Multiplicative.ofAdd 1)
    (N : Subgroup (Subgroup.closure (Set.range target))) [N.Normal] :
    SocleNormalGeneratorBound (Subgroup.closure (Set.range target) ⧸ N) 2 := by
  let K := Subgroup.closure (Set.range lifted)
  have hsurj : Function.Surjective (projection linear K) := by
    intro c
    have hp : ∃ m : Fin 12, (Multiplicative.ofAdd (1 : ZMod 12))^m.val = c := by
      revert c; decide +kernel
    obtain ⟨m,hm⟩ := hp
    refine ⟨closureGenerators lifted j ^ m.val,?_⟩
    rw [map_pow]
    change (lifted j).right ^ m.val = c
    rw [hj,hm]
  let f : K →* Equiv.Perm (Fin 16) := (literalAction e).comp K.subtype
  let q := GeneratedLiteralImage.toTop f (closureGenerators lifted) target (Equiv.refl _)
    (closureGenerators_full lifted) hbinding
  have hq : Function.Surjective q := GeneratedLiteralImage.toTop_surjective
    f (closureGenerators lifted) target (Equiv.refl _) (closureGenerators_full lifted) hbinding
  exact actual_socle_of_surjective K hsurj ((QuotientGroup.mk' N).comp q)
    ((QuotientGroup.mk'_surjective N).comp hq)
end SymmetricSubgroupAsymptotics.BinaryPlaneCyclicTwelveSocles
end
