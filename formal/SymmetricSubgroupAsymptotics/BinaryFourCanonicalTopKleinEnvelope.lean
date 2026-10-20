import SymmetricSubgroupAsymptotics.BinaryFourCanonicalTopBinaryQuotients
import SymmetricSubgroupAsymptotics.BinaryFourCanonicalLocalMiddleInclusion

/-! The retained top Klein coordinate occupies the SECOND active plane.
Its conjugation law includes the actual odd reflection. This is an exact
map on the literal Klein kernel, not a dimension-only replacement. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryFourCanonicalTopKleinEnvelope
open BinaryFourBlockAugmentation BinaryFourSymmetricBlockActions

local instance : Fintype Klein :=
  Fintype.ofEquiv Local (Multiplicative.ofAdd : Local ≃ Klein)
local instance : Fintype Ternary :=
  Fintype.ofEquiv (ZMod 3) (Multiplicative.ofAdd : ZMod 3 ≃ Ternary)
local instance : Fintype Binary :=
  Fintype.ofEquiv (ZMod 2) (Multiplicative.ofAdd : ZMod 2 ≃ Binary)

local instance : DecidableEq Klein := fun x y =>
  if h : x.toAdd = y.toAdd then isTrue (Multiplicative.toAdd.injective h)
  else isFalse (fun he => h (congrArg Multiplicative.toAdd he))
local instance : DecidableEq Ternary := fun x y =>
  if h : x.toAdd = y.toAdd then isTrue (Multiplicative.toAdd.injective h)
  else isFalse (fun he => h (congrArg Multiplicative.toAdd he))
local instance : DecidableEq Binary := fun x y =>
  if h : x.toAdd = y.toAdd then isTrue (Multiplicative.toAdd.injective h)
  else isFalse (fun he => h (congrArg Multiplicative.toAdd he))


private def value (g : SymmetricComplement) : SymmetricEnvelope :=
  (0,0,localCycle.symm g.left.left.toAdd)

def kleinEmbedding : BinaryFourSymmetricKleinNormalCover.klein →*
    Multiplicative SymmetricEnvelope where
  toFun x := Multiplicative.ofAdd (value x.1)
  map_one' := by decide +kernel
  map_mul' x y := by
    have h : ∀ p q : Klein,
        value ((⟨⟨p,1⟩,1⟩ : SymmetricComplement)*(⟨⟨q,1⟩,1⟩ : SymmetricComplement)) =
          value (⟨⟨p,1⟩,1⟩ : SymmetricComplement) +
          value (⟨⟨q,1⟩,1⟩ : SymmetricComplement) := by decide +kernel
    obtain ⟨hxz,hxb⟩ := (BinaryFourSymmetricKleinNormalCover.mem_klein x.1).mp x.2
    obtain ⟨hyz,hyb⟩ := (BinaryFourSymmetricKleinNormalCover.mem_klein y.1).mp y.2
    rcases x with ⟨⟨⟨p,z⟩,b⟩,hx⟩
    rcases y with ⟨⟨⟨q,t⟩,c⟩,hy⟩
    change z = 1 at hxz
    change b = 1 at hxb
    change t = 1 at hyz
    change c = 1 at hyb
    subst z; subst b; subst t; subst c
    exact congrArg Multiplicative.ofAdd (h p q)

theorem kleinEmbedding_injective : Function.Injective kleinEmbedding := by
  intro x y h
  have hp : x.1.left.left = y.1.left.left := by
    apply Multiplicative.toAdd.injective
    apply localCycle.symm.injective
    exact congrArg (fun z : Multiplicative SymmetricEnvelope => z.toAdd.2.2) h
  obtain ⟨hxz,hxb⟩ := (BinaryFourSymmetricKleinNormalCover.mem_klein x.1).mp x.2
  obtain ⟨hyz,hyb⟩ := (BinaryFourSymmetricKleinNormalCover.mem_klein y.1).mp y.2
  apply Subtype.ext
  exact SemidirectProduct.ext
    (SemidirectProduct.ext hp (hxz.trans hyz.symm)) (hxb.trans hyb.symm)

theorem conjugate (g : SymmetricComplement)
    (x : BinaryFourSymmetricKleinNormalCover.klein) :
    (kleinEmbedding (MulAut.conjNormal g x)).toAdd =
      symmetricEnvelopeRepresentation g (kleinEmbedding x).toAdd := by
  have h : ∀ (p : Klein) (z : Ternary) (b : Binary) (q : Klein),
      value ((⟨⟨p,z⟩,b⟩ : SymmetricComplement)*(⟨⟨q,1⟩,1⟩ : SymmetricComplement)*
        (⟨⟨p,z⟩,b⟩ : SymmetricComplement)⁻¹) =
      symmetricEnvelopeRepresentation (⟨⟨p,z⟩,b⟩ : SymmetricComplement)
        (value (⟨⟨q,1⟩,1⟩ : SymmetricComplement)) := by decide +kernel
  obtain ⟨hxz,hxb⟩ := (BinaryFourSymmetricKleinNormalCover.mem_klein x.1).mp x.2
  rcases g with ⟨⟨p,z⟩,b⟩
  rcases x with ⟨⟨⟨q,t⟩,c⟩,hx⟩
  change t = 1 at hxz
  change c = 1 at hxb
  subst t; subst c
  exact h p z b q

/-- Actual normal binary subgroups of the unquotiented S4 top retain
this same injective coordinate, without asserting an ambient bound is
inherited by an arbitrary subgroup. -/
def binaryNormalEmbedding (H : Subgroup SymmetricComplement) [H.Normal]
    (hH : IsPGroup 2 H) : H →* Multiplicative SymmetricEnvelope :=
  kleinEmbedding.comp
    (Subgroup.inclusion (BinaryFourCanonicalTopBinaryQuotients.s4_binary_normal_le_klein H hH))

theorem binaryNormalEmbedding_injective (H : Subgroup SymmetricComplement) [H.Normal]
    (hH : IsPGroup 2 H) : Function.Injective (binaryNormalEmbedding H hH) :=
  kleinEmbedding_injective.comp (Subgroup.inclusion_injective _)

end SymmetricSubgroupAsymptotics.BinaryFourCanonicalTopKleinEnvelope
end
