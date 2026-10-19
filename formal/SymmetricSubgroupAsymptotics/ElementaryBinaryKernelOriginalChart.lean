import SymmetricSubgroupAsymptotics.SixPairNonbinaryQuotientCubic
import SymmetricSubgroupAsymptotics.SixPairB6CubicActualCoordinates
import SymmetricSubgroupAsymptotics.MinimalNormalCompositionCharts

/-! Every actual elementary binary normal kernel has its literal conjugation
module on the supplied original top. No splitting or module census is
required; the chart is built directly from the square-one law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped IsMulCommutative
namespace SymmetricSubgroupAsymptotics
namespace ElementaryBinaryKernelOriginalChart

variable {G T : Type} [Group G] [Group T]
    (top : G →* T) (htop : Function.Surjective top)
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
def kernelModule : Rep (ZMod 2) T :=
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

end ElementaryBinaryKernelOriginalChart
end SymmetricSubgroupAsymptotics
end
