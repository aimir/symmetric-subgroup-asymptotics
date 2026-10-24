import SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveRectangularCommutator
import SymmetricSubgroupAsymptotics.ExactHomSubgroupCardinality
import SymmetricSubgroupAsymptotics.FiniteFieldMultiplicationOrthogonality
import SymmetricSubgroupAsymptotics.CFSGHeisenbergFiniteFieldIsotropy

/-! Three layers of the SAME arbitrary subgroup of the literal positive Ree
group. Only additive prime-field subspaces are used. The first image pairs
with the middle image of the first-kernel intersection, rather than with a
putative abelian two-coordinate quotient of the whole positive group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoSubgroupCoordinateLayers

open CFSGReeGTwoFieldParameters CFSGReeGTwoOriginalPositiveSubgroup
open CFSGReeGTwoPositiveCoordinates CFSGReeGTwoPositiveCentre
open CFSGReeGTwoPositiveFirstQuotient CFSGReeGTwoPositiveRectangularCommutator

def centralKernelHom (m : ℕ) : Multiplicative (Field m) →* firstKernel m :=
  (centralHom m).codRestrict (firstKernel m) (fun c => by
    apply (chart_mem_firstKernel_iff m _).mpr
    rfl)

theorem centralKernelHom_injective (m : ℕ) : Function.Injective (centralKernelHom m) := by
  intro a b hab
  apply centralHom_injective m
  exact congrArg (fun z : firstKernel m => z.val) hab

theorem centralKernelHom_range (m : ℕ) :
    (centralKernelHom m).range = (middleHom m).ker := by
  ext u
  constructor
  · rintro ⟨c, rfl⟩
    change Multiplicative.ofAdd
      (coordinates m (fixedPositiveChart m ![0, 0, c.toAdd]) 1) = 1
    rw [coordinates_chart]
    rfl
  · intro hu
    change middleHom m u = 1 at hu
    have h0 := (mem_firstKernel_iff m u.val).mp u.property
    have h1 : coordinates m u.val 1 = 0 :=
      congrArg Multiplicative.toAdd hu
    refine ⟨Multiplicative.ofAdd (coordinates m u.val 2), ?_⟩
    apply Subtype.ext
    change fixedPositiveChart m ![0, 0, coordinates m u.val 2] = u.val
    rw [← chart_coordinates m u.val]
    simp only [coordinates_chart]
    apply congrArg (fixedPositiveChart m)
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · rfl

def centralLayer (m : ℕ) (L : Subgroup (fixedPositiveGroup m)) : AddSubgroup (Field m) :=
  (L.comap (centralHom m)).toAddSubgroup'

def firstLayer (m : ℕ) (L : Subgroup (fixedPositiveGroup m)) : AddSubgroup (Field m) :=
  (L.map (firstHom m)).toAddSubgroup'

def middleLayer (m : ℕ) (L : Subgroup (fixedPositiveGroup m)) : AddSubgroup (Field m) :=
  ((L.comap (firstKernel m).subtype).map (middleHom m)).toAddSubgroup'

theorem centralLayer_ne_top (m : ℕ) (L : Subgroup (fixedPositiveGroup m))
    (hL : ¬ (centralHom m).range ≤ L) : centralLayer m L ≠ ⊤ := by
  intro he
  apply hL
  rintro g ⟨c, rfl⟩
  change c.toAdd ∈ centralLayer m L
  rw [he]
  trivial

theorem layers_product_mem (m : ℕ) (L : Subgroup (fixedPositiveGroup m))
    (a : Field m) (ha : a ∈ firstLayer m L)
    (b : Field m) (hb : b ∈ middleLayer m L) : a * b ∈ centralLayer m L := by
  change Multiplicative.ofAdd a ∈ L.map (firstHom m) at ha
  change Multiplicative.ofAdd b ∈
    (L.comap (firstKernel m).subtype).map (middleHom m) at hb
  obtain ⟨x, hx, hxa⟩ := ha
  obtain ⟨y, hy, hyb⟩ := hb
  have hxa' : coordinates m x 0 = a := congrArg Multiplicative.toAdd hxa
  have hyb' : coordinates m y.val 1 = b := congrArg Multiplicative.toAdd hyb
  change Multiplicative.ofAdd (a * b) ∈ L.comap (centralHom m)
  rw [← hxa', ← hyb']
  exact product_mem_central_preimage m L x y.val hx hy y.property

private def additiveLayerEquiv (m : ℕ) (A : Subgroup (Multiplicative (Field m))) :
    A ≃ A.toAddSubgroup' where
  toFun x := ⟨x.val.toAdd, x.property⟩
  invFun x := ⟨Multiplicative.ofAdd x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_layers (m : ℕ) (L : Subgroup (fixedPositiveGroup m)) :
    Nat.card L = Nat.card (centralLayer m L) * Nat.card (middleLayer m L) *
      Nat.card (firstLayer m L) := by
  letI : Finite (fixedPositiveGroup m) :=
    Finite.of_equiv (Fin 3 → Field m) (fixedPositiveEquiv m)
  have hr : (firstKernel m).subtype.range = (firstHom m).ker := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact u.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hfirst := ExactHomSubgroupCardinality.card_comap_mul_card_map
    (firstHom m) (firstKernel m).subtype Subtype.val_injective hr L
  have hmiddle := ExactHomSubgroupCardinality.card_comap_mul_card_map
    (middleHom m) (centralKernelHom m) (centralKernelHom_injective m)
      (centralKernelHom_range m) (L.comap (firstKernel m).subtype)
  change Nat.card (L.comap (centralHom m)) *
    Nat.card ((L.comap (firstKernel m).subtype).map (middleHom m)) =
      Nat.card (L.comap (firstKernel m).subtype) at hmiddle
  rw [← hfirst, ← hmiddle]
  rw [Nat.card_congr (additiveLayerEquiv m (L.comap (centralHom m))),
    Nat.card_congr (additiveLayerEquiv m
      ((L.comap (firstKernel m).subtype).map (middleHom m))),
    Nat.card_congr (additiveLayerEquiv m (L.map (firstHom m)))]
  rfl

theorem first_middle_card_mul_le (m : ℕ) (L : Subgroup (fixedPositiveGroup m))
    (hL : ¬ (centralHom m).range ≤ L) :
    Nat.card (firstLayer m L) * Nat.card (middleLayer m L) ≤ Nat.card (Field m) :=
  FiniteFieldMultiplicationOrthogonality.additive_card_mul_le 3
    (centralLayer m L) (firstLayer m L) (middleLayer m L)
    (centralLayer_ne_top m L hL) (layers_product_mem m L)

theorem three_mul_card_le (m : ℕ) (L : Subgroup (fixedPositiveGroup m))
    (hL : ¬ (centralHom m).range ≤ L) :
    3 * Nat.card L ≤ Nat.card (Field m) ^ 2 := by
  have hA := CFSGHeisenbergFiniteFieldIsotropy.proper_additive_card_mul_prime_le
    3 (centralLayer m L) (centralLayer_ne_top m L hL)
  have hVW := first_middle_card_mul_le m L hL
  calc
    3 * Nat.card L = (3 * Nat.card (centralLayer m L)) *
        (Nat.card (firstLayer m L) * Nat.card (middleLayer m L)) := by
      rw [card_layers]
      ring
    _ ≤ Nat.card (Field m) * Nat.card (Field m) := Nat.mul_le_mul hA hVW
    _ = Nat.card (Field m) ^ 2 := (pow_two _).symm

theorem three_field_card_le_index (m : ℕ) (L : Subgroup (fixedPositiveGroup m))
    (hL : ¬ (centralHom m).range ≤ L) : 3 * Nat.card (Field m) ≤ L.index := by
  letI : Finite (fixedPositiveGroup m) :=
    Finite.of_equiv (Fin 3 → Field m) (fixedPositiveEquiv m)
  have hc : Nat.card L * L.index = Nat.card (Field m) ^ 3 := by
    rw [L.card_mul_index, fixedPositiveGroup_card, field_card]
  have hb := Nat.mul_le_mul_right L.index (three_mul_card_le m L hL)
  have hq : 0 < Nat.card (Field m) ^ 2 := pow_pos (Nat.card_pos (α := Field m)) _
  have hprod : Nat.card (Field m) ^ 2 * (3 * Nat.card (Field m)) ≤
      Nat.card (Field m) ^ 2 * L.index := by
    calc
      _ = 3 * (Nat.card L * L.index) := by rw [hc]; ring
      _ ≤ _ := by simpa only [Nat.mul_assoc] using hb
  exact Nat.le_of_mul_le_mul_left hprod hq

end SymmetricSubgroupAsymptotics.CFSGReeGTwoSubgroupCoordinateLayers
