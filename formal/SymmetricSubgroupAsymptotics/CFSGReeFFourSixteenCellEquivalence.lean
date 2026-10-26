import SymmetricSubgroupAsymptotics.CFSGReeFFourShortWordBlockSeparation
import SymmetricSubgroupAsymptotics.CFSGReeFFourUniqueFixedInversionCover
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedSubgroupPeeling

/-! The original sixteen-cell map is injective and surjective. Distinct
indices are separated by the proved actual Weyl block action; factors
inside one cell are separated by opposed-subgroup coordinates. Coverage
uses the original short-word cover and its genuine sign factorization.
No whole-group order or class count is asserted here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourSixteenCellEquivalence
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourOppositionFixedPositiveNegative
open CFSGReeFFourFixedBruhatCover CFSGReeFFourFixedBorelCardinality
open CFSGReeFFourShortPairedWeylMenu CFSGReeFFourFixedSubgroupPeeling
open CFSGReeFFourShortWordBlockSeparation CFSGReeFFourFixedWordClassification
open CFSGFFourOriginalBruhatCells CFSGReeFFourOriginalWeylWords CFSGOpposedSubgroupPeeling
open CFSGCentralTwistedProductCoordinates

abbrev Cell (m : ℕ) (i : Fin 16) :=
  fixedBorel m × inversionPart (fixedPositive m) (fixedNegative m) (shortModelWord m i)

def cellMap (m : ℕ) : (Σ i : Fin 16, Cell m i) → originalModelFixed m :=
  fun z => z.2.1.val*shortModelWord m z.1*z.2.2.val

private theorem within_cell_injective (m : ℕ) (i : Fin 16) :
    Function.Injective (fun z : Cell m i => z.1.val*shortModelWord m i*z.2.val) := by
  let R := inversionPart (fixedPositive m) (fixedNegative m) (shortModelWord m i)
  exact shifted_product_factors_injective (fixedBorel m) (fixedNegative m)
    (shortModelWord m i) R.subtype Subtype.val_injective
    (fixedBorel_negative_disjoint m) (fun v => v.property.2)

private theorem cell_indices_eq (m : ℕ) (i j : Fin 16)
    (b : fixedBorel m)
    (u : inversionPart (fixedPositive m) (fixedNegative m) (shortModelWord m i))
    (c : fixedBorel m)
    (v : inversionPart (fixedPositive m) (fixedNegative m) (shortModelWord m j))
    (he : b.val*shortModelWord m i*u.val=c.val*shortModelWord m j*v.val) : i=j := by
  let left := c.val⁻¹*b.val
  let right := u.val*v.val⁻¹
  have hleft : left∈fixedBorel m :=
    (fixedBorel m).mul_mem ((fixedBorel m).inv_mem c.property) b.property
  have hright : right∈fixedBorel m :=
    (fixedBorel m).mul_mem (positive_le_borel m u.property.1)
      ((fixedBorel m).inv_mem (positive_le_borel m v.property.1))
  have hword : left*shortModelWord m i*right=shortModelWord m j := by
    calc
      _=c.val⁻¹*(b.val*shortModelWord m i*u.val)*v.val⁻¹ := by dsimp only [left,right]; group
      _=c.val⁻¹*(c.val*shortModelWord m j*v.val)*v.val⁻¹ := by rw [he]
      _=_ := by group
  have hmodel := congrArg (fun g : originalModelFixed m => g.val) hword
  change left.val*modelWeylWord (Field m) (expandPaired (shortWord i))*right.val =
    modelWeylWord (Field m) (expandPaired (shortWord j)) at hmodel
  have hblocks := model_cell_word_block_unique (Field m)
    (expandPaired (shortWord i)) (expandPaired (shortWord j))
    left.val right.val hleft hright hmodel
  exact short_block_action_injective hblocks

theorem cellMap_injective (m : ℕ) : Function.Injective (cellMap m) := by
  rintro ⟨i,b,u⟩ ⟨j,c,v⟩ he
  have hij : i=j := cell_indices_eq m i j b u c v he
  subst j
  have hp : (b,u)=(c,v) := within_cell_injective m i he
  cases hp
  rfl

theorem cellMap_surjective (m : ℕ) : Function.Surjective (cellMap m) := by
  intro g
  obtain ⟨u,d,i,v,he⟩ := exists_short_fixed_cell m g
  obtain ⟨p,hp,b,hb,hprod,hconj⟩ := fixed_sign_factorization m (shortWord i) v.val v.property
  let a := u.val*d.val*(shortModelWord m i*p*(shortModelWord m i)⁻¹)
  have ha : a∈fixedBorel m :=
    (fixedBorel m).mul_mem
      ((fixedBorel m).mul_mem (positive_le_borel m u.property) (diagonal_le_borel m d.property))
      (positive_le_borel m hconj)
  refine ⟨⟨i,⟨⟨a,ha⟩,⟨b,hb⟩⟩⟩,?_⟩
  change a*shortModelWord m i*b=g
  calc
    _=u.val*d.val*shortModelWord m i*(p*b) := by dsimp only [a]; group
    _=u.val*d.val*shortModelWord m i*v.val := by rw [←hprod]
    _=g := he.symm

theorem cellMap_bijective (m : ℕ) : Function.Bijective (cellMap m) :=
  ⟨cellMap_injective m,cellMap_surjective m⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourSixteenCellEquivalence
