import SymmetricSubgroupAsymptotics.SixPairNonbinaryQuotientCubic
import SymmetricSubgroupAsymptotics.SixPairB6CubicActualCoordinates
import SymmetricSubgroupAsymptotics.MinimalNormalCompositionCharts

/-! All-normal B6 sources for the entire actual elementary-binary-by-C3
class of transitive twelve-point actions. The original kernel exponent
constructs its vector module, and original point geometry constructs all
joint coordinates. Neither is a project-owned source-bound premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped IsMulCommutative
namespace SymmetricSubgroupAsymptotics
namespace SixPairB6ElementaryCubic

variable {G : Type} [Group G]
    (top : G →* CyclicThree) (htop : Function.Surjective top)
    (hsquare : ∀ k : top.ker, k^2 = 1)

include hsquare in
private theorem kernel_commutative (x y : top.ker) : x*y = y*x := by
  have hinv : ∀ a : top.ker, a⁻¹ = a := fun a =>
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hsquare a)
  calc
    x*y = (x*y)⁻¹ := (hinv _).symm
    _ = y⁻¹*x⁻¹ := mul_inv_rev _ _
    _ = y*x := by rw [hinv,hinv]

variable [Finite G]

include hsquare in
/-- The elementary chart is constructed from exponent2, without a
selected module/isomorphism certificate. -/
def elementaryChart : ElementaryMinimalNormalChart top.ker := by
  letI : IsMulCommutative top.ker := IsMulCommutative.of_comm (kernel_commutative top hsquare)
  letI : Module (ZMod 2) (Additive top.ker) :=
    AddCommGroup.zmodModule (n := 2) (fun x => by
      apply Additive.toMul.injective
      exact hsquare x.toMul)
  exact {
    p := 2
    p_prime := Nat.prime_two
    primeFact := ⟨Nat.prime_two⟩
    V := Additive top.ker
    addCommGroup := inferInstance
    module := inferInstance
    finiteDimensional := Module.Finite.of_finite
    equiv := elementaryAdditiveChart top.ker }

include hsquare htop in
/-- Conjugation factored through the ACTUAL cubic quotient map. -/
def kernelModule : Rep (ZMod 2) CyclicThree :=
  Rep.of ((elementaryChart top hsquare).quotientRepresentation.ρ.comp
    (QuotientGroup.quotientKerEquivOfSurjective top htop).symm.toMonoidHom)

include hsquare htop in
/-- Its chart identifies precisely the kernel of the original top map. -/
def originalChart : OriginalKernelModuleChart top (kernelModule top htop hsquare) where
  equiv := (elementaryChart top hsquare).equiv.symm
  conjugate := by
    intro g v
    let C := elementaryChart top hsquare
    let e := QuotientGroup.quotientKerEquivOfSurjective top htop
    have he : e.symm (top g) = QuotientGroup.mk' top.ker g := by
      apply e.injective
      rw [e.apply_symm_apply]
      rfl
    change (C.equiv.symm (Multiplicative.ofAdd
      (C.quotientRepresentation.ρ (e.symm (top g)) v)) : G) =
        g*(C.equiv.symm (Multiplicative.ofAdd v) : G)*g⁻¹
    rw [he]
    obtain ⟨k,hk⟩ := C.equiv.surjective (Multiplicative.ofAdd v)
    have hv : (C.equiv k).toAdd = v := congrArg Multiplicative.toAdd hk
    rw [← hv,C.quotientRepresentation_apply]
    simp only [ofAdd_toAdd,C.equiv.symm_apply_apply]
    rfl

section Original
variable {U : Subgroup (Equiv.Perm (Fin 12))}
    [MulAction.IsPretransitive U (Fin 12)]
    (F : BinaryPairFrame U (Fin 6))
    (t : U →* CyclicThree) (ht : Function.Surjective t)
    (hE : ∀ k : t.ker, k^2 = 1)
include F t ht hE

/-- One reusable source for every original normal denominator in this
whole structural class. No literal client or module chart is required. -/
def quotientCertificate (hKP : KovacsPraegerAbelianizationBound)
    (N : Subgroup U) [N.Normal] : PreE7B6QuotientCertificate (U ⧸ N) :=
  SixPairNonbinaryQuotientCubic.quotientCertificate F t ht
    (kernelModule t ht hE) (originalChart t ht hE)
    (SixPairB6CubicActualCoordinates.coordinates t ht
      (kernelModule t ht hE) (originalChart t ht hE)) hKP N

/-- Exact original action source, suitable for actual source-catalogue rows. -/
def actionCertificate (hKP : KovacsPraegerAbelianizationBound) :
    Non2UnipotentPrefixFiniteMenu.PreE7B6ActionCertificate U where
  blockChart := Non2UnipotentPrefixFiniteMenu.sixPairBlockChart F
  preserves := Non2UnipotentPrefixFiniteMenu.sixPairBlockChart_preserves F
  quotient N := quotientCertificate F t ht hE hKP N.1

end Original
end SixPairB6ElementaryCubic
end SymmetricSubgroupAsymptotics
end
