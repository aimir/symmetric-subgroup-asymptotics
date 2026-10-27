import SymmetricSubgroupAsymptotics.FiniteExtensionFullTopBinaryKernelCount
import SymmetricSubgroupAsymptotics.ActualFullWreathFamily
import SymmetricSubgroupAsymptotics.FinitePermutationalWreathInstance
import SymmetricSubgroupAsymptotics.ActualWreathComplementMonomialCoordinates

/-! Complete small-base envelope at a SAME top. Charges only the actual
base order and the chosen generating tuple of Q, not |Q|. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualFullWreathSmallBaseCount
open PermutationalWreathProduct
local instance subgroupFinite {G : Type} [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun K : Subgroup G => (K : Set G)) SetLike.coe_injective
variable {C Q I : Type} [Group C] [Group Q] [MulAction Q I]
    [Finite C] [Finite Q] [Finite I]

private def encode (L : ActualFullWreathFamily.Family C Q I) :
    FiniteExtensionFullImageRestrictedKernelCount.Family
      (rightHom (D := C) (Q := Q) (I := I)) (fun _ => True) :=
  ⟨L.val,L.property.1,trivial⟩

private theorem encode_injective : Function.Injective (encode (C := C) (Q := Q) (I := I)) := by
  intro L M h
  exact Subtype.ext (congrArg (fun U :
    FiniteExtensionFullImageRestrictedKernelCount.Family
      (rightHom (D := C) (Q := Q) (I := I)) (fun _ => True) => U.val) h)

theorem card_family_le (a : ℕ) (ha : Nat.card C≤2^a) {d : ℕ}
    (f : Fin d → Q) (hf : Subgroup.closure (Set.range f)=⊤) :
    Nat.card (ActualFullWreathFamily.Family C Q I)≤
      2^((Nat.card I*a)*(Nat.card I*a))*Nat.card C^(Nat.card I*d) := by
  have hk : Nat.card (rightHom (D := C) (Q := Q) (I := I)).ker=
      Nat.card C^Nat.card I :=
    (Nat.card_congr ActualWreathComplementMonomialCoordinates.fullBaseChart.toEquiv).trans Nat.card_fun
  have hb : Nat.card (rightHom (D := C) (Q := Q) (I := I)).ker≤2^(Nat.card I*a) := by
    rw [hk]
    calc
      _≤(2^a)^Nat.card I := Nat.pow_le_pow_left ha _
      _=_ := by rw [←pow_mul,Nat.mul_comm a]
  have hs : Function.Surjective (rightHom (D := C) (Q := Q) (I := I)) :=
    fun q => ⟨⟨1,q⟩,rfl⟩
  have hh := (Nat.card_le_card_of_injective encode encode_injective).trans
    (FiniteExtensionFullTopBinaryKernelCount.card_fullImage_le rightHom hs (Nat.card I*a) hb f hf)
  simpa only [hk,←pow_mul] using hh

end SymmetricSubgroupAsymptotics.ActualFullWreathSmallBaseCount
