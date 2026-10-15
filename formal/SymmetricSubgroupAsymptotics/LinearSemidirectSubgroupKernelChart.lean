import SymmetricSubgroupAsymptotics.LinearSemidirectUniformNormalGenerators
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators
import Mathlib.Algebra.Module.ZMod

/-! The elementary kernel chart of an arbitrary subgroup of a linear
semidirect product. Its coordinate space is the retained translation
submodule and its quotient is the actual projection image. No pure
complement or splitting of the subgroup is assumed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.LinearSemidirectSubgroupKernelChart

open SemidirectProduct LinearSemidirectCoprimeSocleBounds

variable {p : ℕ} [Fact p.Prime]
  {R V : Type} [Group R] [AddCommGroup V] [Module (ZMod p) V]
  [FiniteDimensional (ZMod p) V]
  (rho : R →* (V ≃ₗ[ZMod p] V)) (K : Subgroup (Model rho))

def projection : K →* R := (rightHom : Model rho →* R).comp K.subtype

abbrev Image := (projection rho K).range

def translationAddSubgroup : AddSubgroup V where
  carrier := {v | (inl (Multiplicative.ofAdd v) : Model rho) ∈ K}
  zero_mem' := by
    change (inl (1 : Multiplicative V) : Model rho) ∈ K
    simpa only [map_one] using K.one_mem
  add_mem' := by
    intro v w hv hw
    change (inl (Multiplicative.ofAdd v * Multiplicative.ofAdd w) : Model rho) ∈ K
    rw [map_mul]
    exact K.mul_mem hv hw
  neg_mem' := by
    intro v hv
    change (inl (Multiplicative.ofAdd v)⁻¹ : Model rho) ∈ K
    rw [map_inv]
    exact K.inv_mem hv

def translationSpace : Submodule (ZMod p) V :=
  AddSubgroup.toZModSubmodule p (translationAddSubgroup rho K)

def kernel : Subgroup K := (projection rho K).ker

instance : (kernel rho K).Normal :=
  inferInstanceAs (projection rho K).ker.Normal

omit [FiniteDimensional (ZMod p) V] in
theorem kernel_right (x : kernel rho K) : ((x : K) : Model rho).right = 1 :=
  MonoidHom.mem_ker.mp x.property

omit [FiniteDimensional (ZMod p) V] in
theorem inl_left_eq (x : kernel rho K) :
    (inl ((x : K) : Model rho).left : Model rho) = ((x : K) : Model rho) := by
  apply SemidirectProduct.ext
  · rfl
  · exact (kernel_right rho K x).symm

def kernelEquiv : kernel rho K ≃* Multiplicative (translationSpace rho K) where
  toFun x := Multiplicative.ofAdd
    ⟨((x : K) : Model rho).left.toAdd, by
      change (inl ((x : K) : Model rho).left : Model rho) ∈ K
      rw [inl_left_eq rho K x]
      exact (x : K).property⟩
  invFun v := ⟨⟨inl (Multiplicative.ofAdd v.toAdd.1), v.toAdd.property⟩, rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact inl_left_eq rho K x
  right_inv v := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change (((x : K) : Model rho).left *
        linearAction rho ((x : K) : Model rho).right ((y : K) : Model rho).left).toAdd =
      ((x : K) : Model rho).left.toAdd + ((y : K) : Model rho).left.toAdd
    rw [kernel_right rho K x,map_one]
    rfl

def chart : ElementaryMinimalNormalChart (kernel rho K) where
  p := p
  p_prime := Fact.out
  V := translationSpace rho K
  equiv := kernelEquiv rho K

def quotientEquiv : K ⧸ kernel rho K ≃* Image rho K :=
  QuotientGroup.quotientKerEquivRange (projection rho K)

/-- The coordinate inclusion intertwines original conjugation with the
actual projected linear action, even for a sign-carrying affine lift. -/
def inclusion :
    Representation.IntertwiningMap (A := ZMod p) (V := translationSpace rho K) (W := V)
    ((chart rho K).quotientRepresentation.ρ.comp
      (QuotientGroup.mk' (kernel rho K)))
        ((linearRepresentation rho).comp (projection rho K)) where
  toLinearMap := (translationSpace rho K).subtype
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    let e : kernel rho K := (kernelEquiv rho K).symm (Multiplicative.ofAdd v)
    have hev : ((chart rho K).equiv e).toAdd = v :=
      congrArg Multiplicative.toAdd ((kernelEquiv rho K).apply_symm_apply _)
    have h := (chart rho K).quotientRepresentation_apply g e
    rw [hev] at h
    have hc := congrArg (fun w : translationSpace rho K => (w : V)) h
    change Subtype.val (p := fun v : V => v ∈ translationSpace rho K)
      ((chart rho K).quotientRepresentation.ρ
        (QuotientGroup.mk' (kernel rho K) g) v) =
      (((g : Model rho) * inl (Multiplicative.ofAdd (v : V)) *
        (g : Model rho)⁻¹).left).toAdd at hc
    rw [conjugate_translation] at hc
    exact hc

theorem inclusion_injective : Function.Injective (inclusion rho K) :=
  fun _ _ h => Subtype.ext h

def imageRepresentation : Representation (ZMod p) (Image rho K) V :=
  (linearRepresentation rho).comp (projection rho K).range.subtype

theorem uniform (t : ℕ)
    (h : UniformSubrepresentationGeneratorBound (imageRepresentation rho K) t) :
    UniformSubrepresentationGeneratorBound (chart rho K).quotientRepresentation.ρ t := by
  apply UniformSubrepresentationGeneratorBound.of_comp
    (chart rho K).quotientRepresentation.ρ (QuotientGroup.mk' (kernel rho K))
  have hfull : UniformSubrepresentationGeneratorBound
      ((linearRepresentation rho).comp (projection rho K)) t :=
    UniformSubrepresentationGeneratorBound.comp_of_surjective
      (imageRepresentation rho K) (projection rho K).rangeRestrict
      (projection rho K).rangeRestrict_surjective h
  exact hfull.of_injective (inclusion rho K) (inclusion_injective rho K)

end SymmetricSubgroupAsymptotics.LinearSemidirectSubgroupKernelChart

end
