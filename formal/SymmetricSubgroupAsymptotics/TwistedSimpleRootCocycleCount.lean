import SymmetricSubgroupAsymptotics.TwistedCocycleAssociatedHom
import SymmetricSubgroupAsymptotics.SimpleNormalOuterRootFibreCount

/-! Root cocycles with genuine full local image inject into the exact
semisimple outer fibre. The arbitrary conjugation twist is retained.
The fullness predicate is essential and is never discarded. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwistedSimpleRootCocycleCount
open TwistedMonomialCocycleFrame TwistedCocycleAssociatedHom

local instance homFinite {P B : Type*} [Group P] [Group B] [Finite P] [Finite B] :
    Finite (P →* B) :=
  Finite.of_injective (fun f : P →* B => (f : P → B)) DFunLike.coe_injective

variable {H A U : Type*} [Group H] [Finite H] [Group A] [Finite A]
    [IsSimpleGroup A] [Group U] [Finite U]
variable (α : H →* MulAut A) (β : H →* U) (ι : A →* U)
    (hcompat : ∀ h a,ι (α h a)=β h*ι a*(β h)⁻¹)

abbrev FullRoot := {c : Cocycle α // Function.Surjective (associatedHom α β ι hcompat c)}

def zeroAxis : {N : Subgroup U // N.Normal} := ⟨⊥,inferInstance⟩

variable (E : Subgroup U) [E.Normal]
    (hιE : ∀ a,ι a∈E)

def outerMap : H →* U ⧸ ((zeroAxis (U := U)).val⊔E) :=
  (QuotientGroup.mk' ((zeroAxis (U := U)).val⊔E)).comp β

variable (hθ : Function.Surjective (outerMap β E))

def outerEpi : GroupEpimorphism H (U ⧸ ((zeroAxis (U := U)).val⊔E)) :=
  ⟨outerMap β E,hθ⟩

def fibreCode (hιE : ∀ a,ι a∈E)
    (hθ : Function.Surjective (outerMap β E)) (c : FullRoot α β ι hcompat) :
    {φ : GroupEpimorphism H (U ⧸ (zeroAxis (U := U)).val) //
      (quotientOuter E (zeroAxis (U := U))).comp φ.val=(outerEpi β E hθ).val} := by
  let f := associatedHom α β ι hcompat c.val
  refine ⟨⟨(QuotientGroup.mk' (zeroAxis (U := U)).val).comp f,
    (QuotientGroup.mk'_surjective _).comp c.property⟩,?_⟩
  ext h
  change QuotientGroup.mk' ((zeroAxis (U := U)).val⊔E) (ι (c.val.val h)*β h)=
    QuotientGroup.mk' ((zeroAxis (U := U)).val⊔E) (β h)
  have hk : QuotientGroup.mk' ((zeroAxis (U := U)).val⊔E) (ι (c.val.val h))=1 :=
    (QuotientGroup.eq_one_iff _).mpr
      ((le_sup_right : E≤(zeroAxis (U := U)).val⊔E) (hιE _))
  rw [map_mul,hk,one_mul]

include hιE hθ in
theorem fibreCode_injective (hι : Function.Injective ι) :
    Function.Injective (fibreCode α β ι hcompat E hιE hθ) := by
  intro c d h
  apply Subtype.ext
  apply associatedHom_injective α β ι hcompat hι
  ext a
  have hh := DFunLike.congr_fun (congrArg
    (fun z : {φ : GroupEpimorphism H (U ⧸ (zeroAxis (U := U)).val) //
      (quotientOuter E (zeroAxis (U := U))).comp φ.val=(outerEpi β E hθ).val} =>
        z.val.val) h) a
  change QuotientGroup.mk' (zeroAxis (U := U)).val
    (associatedHom α β ι hcompat c.val a)=
    QuotientGroup.mk' (zeroAxis (U := U)).val
    (associatedHom α β ι hcompat d.val a) at hh
  have hinj : Function.Injective (QuotientGroup.mk' (zeroAxis (U := U)).val) :=
    (QuotientGroup.mk' (zeroAxis (U := U)).val).ker_eq_bot_iff.mp
      (QuotientGroup.ker_mk' _)
  exact hinj hh

include hιE hθ in
theorem card_fullRoot_le (C : SemisimpleNormalChart E)
    (e : quotientImage E (zeroAxis (U := U)) ≃* A)
    (hZ : IsCenterless A) (hι : Function.Injective ι) :
    (Nat.card (FullRoot α β ι hcompat) : ℝ) ≤
      Nat.card (A ≃* A)*
        (Real.logb 2 (Nat.card (outerMap β E).ker)/Real.logb 2 (Nat.card A)) := by
  have hi := Nat.card_le_card_of_injective (fibreCode α β ι hcompat E hιE hθ)
    (fibreCode_injective α β ι hcompat E hιE hθ hι)
  have hf := SimpleNormalOuterRootFibreCount.card_root_fibre_le C (zeroAxis (U := U))
    (outerEpi β E hθ) e hZ
  exact (show (Nat.card (FullRoot α β ι hcompat) : ℝ)≤
      (Nat.card {φ : GroupEpimorphism H (U ⧸ (zeroAxis (U := U)).val) //
        (quotientOuter E (zeroAxis (U := U))).comp φ.val=(outerEpi β E hθ).val} : ℝ)
      by exact_mod_cast hi).trans hf

end SymmetricSubgroupAsymptotics.TwistedSimpleRootCocycleCount
