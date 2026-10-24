import SymmetricSubgroupAsymptotics.CFSGReeFFourBorelIntersection
import SymmetricSubgroupAsymptotics.CFSGDisjointSubgroupProductCard

/-! The opposite positive-normalizer envelope has genuine V-D factors.
The disjoint product embeds in N(V), and its cardinal equals that of
N(U) by actual opposition. Finite cardinality gives surjectivity; no
opposition source-square identity or new torus identification is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOppositeBorelFactors
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourFixedBruhatCover
open CFSGReeFFourFixedBorelCardinality CFSGReeFFourBorelIntersection
open CFSGReeFFourFixedAmbientHom

private instance fixedFinite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

theorem negative_le_oppositeBorel (m : ℕ) : fixedNegative m≤oppositeBorel m :=
  (fixedNegative m).le_normalizer

theorem diagonal_le_oppositeBorel (m : ℕ) : fixedDiagonal m≤oppositeBorel m := by
  change fixedDiagonal m≤Subgroup.normalizer (fixedNegative m : Set (originalModelFixed m))
  rw [fixedDiagonal_eq_pairNormalizer]
  exact inf_le_right

private theorem negative_inf_diagonal (m : ℕ) : fixedNegative m⊓fixedDiagonal m=⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp (fixedBorel_negative_disjoint m)
    (diagonal_le_borel m hx.2) hx.1)

def oppositeBorelProduct (m : ℕ) : (fixedNegative m × fixedDiagonal m) → oppositeBorel m :=
  fun p=>⟨p.1.val*p.2.val,(oppositeBorel m).mul_mem
    (negative_le_oppositeBorel m p.1.property) (diagonal_le_oppositeBorel m p.2.property)⟩

theorem oppositeBorelProduct_bijective (m : ℕ) : Function.Bijective (oppositeBorelProduct m) := by
  have hi : Function.Injective (oppositeBorelProduct m) := by
    intro p q he
    exact CFSGDisjointSubgroupProductCard.product_injective (fixedNegative m) (fixedDiagonal m)
      (negative_inf_diagonal m) (congrArg (fun b : oppositeBorel m=>b.val) he)
  apply hi.bijective_of_nat_card_le
  have hv := Nat.card_congr ((MulAut.conj (oppositionFixed m)).subgroupMap (fixedPositive m)).toEquiv
  change Nat.card (fixedPositive m)=Nat.card ((fixedPositive m).map
    (MulAut.conj (oppositionFixed m)).toMonoidHom) at hv
  rw [fixed_positive_image_eq_fixed_negative] at hv
  have hb := Nat.card_congr ((MulAut.conj (oppositionFixed m)).subgroupMap (fixedBorel m)).toEquiv
  change Nat.card (fixedBorel m)=Nat.card ((fixedBorel m).map
    (MulAut.conj (oppositionFixed m)).toMonoidHom) at hb
  rw [fixedBorel_opposition_map] at hb
  have hUD := Nat.card_congr (Equiv.ofBijective (borelProduct m) (borelProduct_bijective m))
  rw [Nat.card_prod] at hUD
  rw [Nat.card_prod,←hv,←hb]
  exact hUD.symm.le

theorem exists_opposite_borel_factors (m : ℕ) (b : oppositeBorel m) :
    ∃v∈fixedNegative m,∃d∈fixedDiagonal m,b.val=v*d := by
  obtain ⟨⟨v,d⟩,he⟩ := (oppositeBorelProduct_bijective m).surjective b
  exact ⟨v.val,v.property,d.val,d.property,(congrArg (fun x : oppositeBorel m=>x.val) he).symm⟩

theorem oppositeBorel_eq_sup (m : ℕ) : oppositeBorel m=fixedNegative m⊔fixedDiagonal m := by
  apply le_antisymm
  · intro b hb
    obtain ⟨v,hv,d,hd,he⟩ := exists_opposite_borel_factors m ⟨b,hb⟩
    change b=v*d at he
    rw [he]
    exact (fixedNegative m⊔fixedDiagonal m).mul_mem
      ((show fixedNegative m≤fixedNegative m⊔fixedDiagonal m from le_sup_left) hv)
      ((show fixedDiagonal m≤fixedNegative m⊔fixedDiagonal m from le_sup_right) hd)
  · exact sup_le (negative_le_oppositeBorel m) (diagonal_le_oppositeBorel m)

end SymmetricSubgroupAsymptotics.CFSGReeFFourOppositeBorelFactors
