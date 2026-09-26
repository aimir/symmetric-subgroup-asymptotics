import SymmetricSubgroupAsymptotics.BinaryInflationKernel

/-! Actual transgression from invariant characters of the original kernel.
A set-theoretic section constructs cocycle/primitive pairs; it is not a group
section and no extension is assumed split. For the binary evaluation quotient,
all original characters vanish on the exact kernel. The resulting equality
concerns mathlib's actual H² inflation kernel, including arbitrary finite
source groups, with no replacement by a numerical proxy. -/
set_option autoImplicit false
noncomputable section
open CategoryTheory

namespace SymmetricSubgroupAsymptotics
namespace BinaryTransgressionExact

variable {G Q : Type} [Group G] [Group Q]
    (β : G →* Q) (hβ : Function.Surjective β)

def quotientSection : Q → G := Function.surjInv hβ

theorem quotientSection_spec (q : Q) : β (quotientSection β hβ q)=q :=
  Function.rightInverse_surjInv hβ q

/-- This remainder lies in the original kernel, before any quotient or chart. -/
def sectionRemainder (x : G) : β.ker :=
  ⟨x*(quotientSection β hβ (β x))⁻¹,by
    change β (x*(quotientSection β hβ (β x))⁻¹)=1
    rw [map_mul,map_inv,quotientSection_spec,mul_inv_cancel]⟩

theorem sectionRemainder_mul_section (x : G) :
    (sectionRemainder β hβ x : G)*quotientSection β hβ (β x)=x := by
  change (x*(quotientSection β hβ (β x))⁻¹)*quotientSection β hβ (β x)=x
  group

theorem sectionRemainder_kernel_mul (n : β.ker) (x : G) :
    sectionRemainder β hβ ((n : G)*x)=n*sectionRemainder β hβ x := by
  apply Subtype.ext
  change ((n : G)*x)*(quotientSection β hβ (β ((n : G)*x)))⁻¹ =
    (n : G)*(x*(quotientSection β hβ (β x))⁻¹)
  rw [map_mul,show β (n : G)=1 from n.2,one_mul]
  group

variable (χ : primeRelativeCharacters 2 β.ker)

/-- A literal cochain on G, obtained from the actual invariant kernel character. -/
def sectionPrimitive (x : G) : ZMod 2 :=
  χ.1 (Additive.ofMul (sectionRemainder β hβ x))

theorem sectionPrimitive_kernel_mul (n : β.ker) (x : G) :
    sectionPrimitive β hβ χ ((n : G)*x)=
      χ.1 (Additive.ofMul n)+sectionPrimitive β hβ χ x := by
  change χ.1 (Additive.ofMul (sectionRemainder β hβ ((n : G)*x))) = _
  rw [sectionRemainder_kernel_mul]
  exact χ.1.map_add (Additive.ofMul n) (Additive.ofMul (sectionRemainder β hβ x))

/-- The differential written as a scalar function on original pairs. -/
def primitiveDifferential (x y : G) : ZMod 2 :=
  sectionPrimitive β hβ χ y - sectionPrimitive β hβ χ (x*y) +
    sectionPrimitive β hβ χ x

theorem differential_kernel_mul_first (n : β.ker) (x y : G) :
    primitiveDifferential β hβ χ ((n : G)*x) y =
      primitiveDifferential β hβ χ x y := by
  unfold primitiveDifferential
  rw [mul_assoc,sectionPrimitive_kernel_mul,sectionPrimitive_kernel_mul]
  abel

/-- Conjugation by the full G is exactly what permits changing the second
representative without losing the original kernel-character value. -/
theorem differential_kernel_mul_second (n : β.ker) (x y : G) :
    primitiveDifferential β hβ χ x ((n : G)*y) =
      primitiveDifferential β hβ χ x y := by
  let n' : β.ker := ⟨x*(n : G)*x⁻¹,
    Subgroup.Normal.conj_mem inferInstance _ n.2 x⟩
  have hn : χ.1 (Additive.ofMul n')=χ.1 (Additive.ofMul n) := χ.2 x n
  have he : x*((n : G)*y)=(n' : G)*(x*y) := by dsimp [n']; group
  unfold primitiveDifferential
  rw [he,sectionPrimitive_kernel_mul,sectionPrimitive_kernel_mul,hn]
  abel

/-- The actual differential factors through the actual pair of quotient maps. -/
theorem primitiveDifferential_factors (x y : G) :
    primitiveDifferential β hβ χ x y =
      primitiveDifferential β hβ χ
        (quotientSection β hβ (β x)) (quotientSection β hβ (β y)) := by
  calc
    _ = primitiveDifferential β hβ χ
        ((sectionRemainder β hβ x : G)*quotientSection β hβ (β x)) y := by
      rw [sectionRemainder_mul_section]
    _ = primitiveDifferential β hβ χ (quotientSection β hβ (β x)) y :=
      differential_kernel_mul_first β hβ χ _ _ _
    _ = primitiveDifferential β hβ χ (quotientSection β hβ (β x))
        ((sectionRemainder β hβ y : G)*quotientSection β hβ (β y)) := by
      rw [sectionRemainder_mul_section]
    _ = _ := differential_kernel_mul_second β hβ χ _ _ _

/-- The quotient cochain is built from the original primitive differential. -/
def sectionCochain (qr : Q × Q) : ZMod 2 :=
  primitiveDifferential β hβ χ
    (quotientSection β hβ qr.1) (quotientSection β hβ qr.2)

theorem sectionCochain_pullback (x y : G) :
    sectionCochain β hβ χ (β x,β y)=primitiveDifferential β hβ χ x y :=
  (primitiveDifferential_factors β hβ χ x y).symm

/-- The descended cochain is a cocycle because its pullback is the actual
scalar coboundary. Surjectivity is used to test every quotient triple. -/
def sectionCocycle : groupCohomology.cocycles₂
    (Rep.trivial (ZMod 2) Q (ZMod 2)) :=
  ⟨sectionCochain β hβ χ,by
    apply (groupCohomology.mem_cocycles₂_iff _).mpr
    intro q r s
    obtain ⟨x,rfl⟩ := hβ q
    obtain ⟨y,rfl⟩ := hβ r
    obtain ⟨z,rfl⟩ := hβ s
    simp only [Representation.trivial_apply,← map_mul,sectionCochain_pullback]
    unfold primitiveDifferential
    rw [mul_assoc]
    abel⟩

def sectionPair : BinaryInflationKernel.primitives β :=
  ⟨(sectionCocycle β hβ χ,sectionPrimitive β hβ χ),by
    intro x y
    exact (sectionCochain_pullback β hβ χ x y).symm⟩

/-- No normalized section is needed: subtracting b(1) recovers χ exactly. -/
theorem restriction_sectionPair :
    BinaryInflationKernel.restriction β (sectionPair β hβ χ)=χ := by
  apply Subtype.ext
  ext n
  change sectionPrimitive β hβ χ (n : G)-sectionPrimitive β hβ χ 1 = χ.1 (Additive.ofMul n)
  have h := sectionPrimitive_kernel_mul β hβ χ n 1
  rw [mul_one] at h
  rw [h]
  abel

include hβ in
/-- Every relative kernel character has a genuine cocycle/primitive pair. -/
theorem restriction_surjective :
    Function.Surjective (BinaryInflationKernel.restriction β) :=
  fun χ => ⟨sectionPair β hβ χ,restriction_sectionPair β hβ χ⟩

omit hβ in
/-- A zero quotient class leaves only an original G-character after a
quotient primitive is subtracted. This retains the actual restriction image. -/
theorem restriction_mem_range_of_class_zero (z : BinaryInflationKernel.primitives β)
    (hz : BinaryInflationKernel.classMap β z=0) :
    BinaryInflationKernel.restriction β z ∈
      LinearMap.range (primeCharacterRestriction 2 β.ker) := by
  have hc : groupCohomology.H2π _ z.1.1=0 := congrArg Subtype.val hz
  obtain ⟨a,ha⟩ := (groupCohomology.H2π_eq_zero_iff z.1.1).mp hc
  let f : G → ZMod 2 := fun g => z.1.2 g-a (β g)
  have hf (x y : G) : f y-f (x*y)+f x=0 := by
    have h₁ := z.2 x y
    have h₂ := congrFun ha (β x,β y)
    change a (β y)-a (β x*β y)+a (β x)=z.1.1 (β x,β y) at h₂
    rw [← map_mul] at h₂
    dsimp [f]
    linear_combination h₁-h₂
  have hf₁ : f 1=0 := by
    simpa only [one_mul,sub_self,zero_add] using hf 1 1
  let ψ : PrimeCharacters 2 G :=
    { toFun := fun g => f g.toMul
      map_zero' := hf₁
      map_add' := fun x y => by
        change f (x.toMul*y.toMul)=f x.toMul+f y.toMul
        linear_combination -(hf x.toMul y.toMul) }
  have h₁ : z.1.2 1=a 1 := by
    change z.1.2 1-a (β 1)=0 at hf₁
    rw [map_one] at hf₁
    exact sub_eq_zero.mp hf₁
  refine ⟨ψ,?_⟩
  apply Subtype.ext
  ext n
  change z.1.2 (n : G)-a (β (n : G)) =
    z.1.2 (n : G)-z.1.2 1
  rw [show β (n : G)=1 from n.2,h₁]

include hβ in
/-- Rank-nullity is proved with an abstract quotient before instantiating
the canonical character-dual quotient. Both maps remain the actual maps. -/
theorem kernel_finrank_eq_relativeHead_of_ker_eq [Finite G]
    (hker : (BinaryInflationKernel.classMap β).ker =
      (BinaryInflationKernel.restriction β).ker) :
    Module.finrank (ZMod 2) (binaryH2Pullback β).ker =
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 β.ker) := by
  letI : Finite Q := Finite.of_surjective β hβ
  have hclass := (BinaryInflationKernel.classMap β).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (BinaryInflationKernel.classMap_surjective β),
    finrank_top] at hclass
  have hrestriction := (BinaryInflationKernel.restriction β).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (restriction_surjective β hβ),finrank_top] at hrestriction
  rw [hker] at hclass
  omega

end BinaryTransgressionExact

section Evaluation
variable (T : Type) [Group T]

/-- Every original binary character vanishes on the exact evaluation kernel. -/
theorem binaryEvaluation_characterRestriction_eq_zero (χ : PrimeCharacters 2 T) :
    primeCharacterRestriction 2
      (AddMonoidHom.toMultiplicativeRight (binaryAbelianizationMap T)).ker χ=0 := by
  apply Subtype.ext
  ext n
  have hn := congrArg
    (fun x : Multiplicative (BinaryAbelianization T) => x.toAdd χ) n.2
  change χ (Additive.ofMul (n : T))=0 at hn
  exact hn

/-- For the canonical quotient, zero class and zero relative restriction
are equivalent on the same space of actual cocycle/primitive pairs. -/
theorem binaryEvaluation_classMap_ker_eq_restriction_ker [Finite T] :
    (BinaryInflationKernel.classMap
      (AddMonoidHom.toMultiplicativeRight (binaryAbelianizationMap T))).ker =
    (BinaryInflationKernel.restriction
      (AddMonoidHom.toMultiplicativeRight (binaryAbelianizationMap T))).ker := by
  apply le_antisymm
  · intro z hz
    obtain ⟨χ,hχ⟩ := BinaryTransgressionExact.restriction_mem_range_of_class_zero _ z
      (LinearMap.mem_ker.mp hz)
    apply LinearMap.mem_ker.mpr
    rw [← hχ,binaryEvaluation_characterRestriction_eq_zero]
  · exact BinaryInflationKernel.restriction_ker_le_classMap_ker _
      (binaryAbelianizationMap_surjective T)

/-- The terminal inflation defect equals the relative head of the exact
original evaluation kernel, for every finite group T. -/
theorem terminalRestrictedInflationKernel_finrank_eq_relativeHead [Finite T] :
    Module.finrank (ZMod 2) (terminalRestrictedInflationKernel T) =
      Module.finrank (ZMod 2) (primeRelativeCharacters 2
        (AddMonoidHom.toMultiplicativeRight (binaryAbelianizationMap T)).ker) :=
  BinaryTransgressionExact.kernel_finrank_eq_relativeHead_of_ker_eq _
    (binaryAbelianizationMap_surjective T)
    (binaryEvaluation_classMap_ker_eq_restriction_ker T)

end Evaluation
end SymmetricSubgroupAsymptotics
