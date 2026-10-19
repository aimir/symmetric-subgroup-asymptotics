import SymmetricSubgroupAsymptotics.TwoBinaryThreePermutationCoordinates
import SymmetricSubgroupAsymptotics.SixPairThreePointNormalTop

/-! Identify the actual transitive three-label top without changing its
physical inclusion or selected cubic element. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwoBinaryThreePermutationCoordinates

variable (T : Subgroup (Equiv.Perm (Fin 3)))
  (hrotation : OddMarkerTernaryChart.rotation∈T)

theorem cubicHom_injective : Function.Injective (cubicHom T hrotation) := by
  intro a b h
  exact OddMarkerTernaryChart.embedding_injective (congrArg Subtype.val h)

theorem cubic_order : orderOf (cubicHom T hrotation (Multiplicative.ofAdd 1))=3 := by
  rw [orderOf_injective (cubicHom T hrotation) (cubicHom_injective T hrotation)]
  rw [orderOf_ofAdd_eq_addOrderOf]
  exact ZMod.addOrderOf_one 3

def cubicEquivOfCardThree (hcard : Nat.card T=3) : CyclicThree ≃* T :=
  MulEquiv.ofBijective (cubicHom T hrotation)
    ((Nat.bijective_iff_injective_and_card (cubicHom T hrotation)).mpr
      ⟨cubicHom_injective T hrotation,by
        rw [hcard,Nat.card_congr Multiplicative.toAdd,Nat.card_zmod]⟩)

def symmetricEquivOfCardSix (hcard : Nat.card T=6) : T ≃* Equiv.Perm (Fin 3) :=
  (MulEquiv.subgroupCongr (Subgroup.eq_top_of_card_eq T (by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin] using hcard))).trans
    Subgroup.topEquiv

end SymmetricSubgroupAsymptotics.TwoBinaryThreePermutationCoordinates
