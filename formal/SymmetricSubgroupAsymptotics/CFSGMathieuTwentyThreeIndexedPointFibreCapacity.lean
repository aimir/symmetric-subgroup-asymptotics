import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreePackedPrefixCertificate
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Dependent-sum counting for the SAME pinned fixed-product automorphisms
and their checked faithful23-point images. Every valid code has one of22
first and21 second addresses. Literal whitelist lengths may vary freely;
no uniform per-prefix bound or aggregate20 capacity is assumed here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeIndexedPointFibreCapacity
open CFSG.Models.Presentations.M23 CFSGMathieuTwentyThreeActualRepresentation
open CFSGMathieuTwentyThreeGoodSylowTwentyThree CFSGMathieuTwentyThreeNormalizedFixedPointFibre
open CFSGMathieuTwentyThreeStabilizerTransversalCover CFSGMathieuTwentyThreeNormalizedFibreChart
open CFSGMathieuTwentyThreePackedPrefixCertificate

abbrev Prefix : Type := First × Second

theorem first_card : Nat.card First = 22 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem second_card : Nat.card Second = 21 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem prefix_card : Nat.card Prefix = 462 := by
  rw [Nat.card_prod,first_card,second_card]

def image (f : pointFibre 0) : Equiv.Perm (Fin 23) :=
  permutationRepresentation (f.val.val pinnedX)

theorem image_injective [IsSimpleGroup Model] : Function.Injective image := by
  intro f g he
  have hx : f.val.val pinnedX = g.val.val pinnedX := permutationRepresentation_injective he
  have ha : f.val.val (pinnedX*pinnedY) = g.val.val (pinnedX*pinnedY) :=
    f.val.property.trans g.val.property.symm
  rw [map_mul,map_mul,hx] at ha
  have hy : f.val.val pinnedY = g.val.val pinnedY := mul_left_cancel ha
  apply Subtype.ext
  apply Subtype.ext
  apply MulEquiv.ext
  intro z
  have hm : f.val.val.toMonoidHom = g.val.val.toMonoidHom := by
    apply MonoidHom.eq_of_eqOn_dense presentation_pair_closure
    rintro w (rfl|rfl)
    · exact hx
    · exact hy
  exact DFunLike.congr_fun hm z

/-- Any genuinely embedded subfibre can be bounded by an indexed finite
cover of its actual permutation images. Overlaps only enlarge the sum. -/
theorem card_le_sum_of_injective [IsSimpleGroup Model]
    {Y I : Type} [Fintype I] (embed : Y → pointFibre 0) (hembed : Function.Injective embed)
    (accepted : I → Finset (Equiv.Perm (Fin 23)))
    (hcover : ∀ y : Y, ∃ i : I, image (embed y) ∈ accepted i) :
    Nat.card Y ≤ ∑ i : I, (accepted i).card := by
  let label : Y → I := fun y => Classical.choose (hcover y)
  have hmem : ∀ y : Y, image (embed y) ∈ accepted (label y) :=
    fun y => Classical.choose_spec (hcover y)
  let encode : Y → (i : I) × accepted i :=
    fun y => ⟨label y,⟨image (embed y),hmem y⟩⟩
  have hinj : Function.Injective encode := by
    intro y z he
    apply hembed
    apply image_injective
    exact congrArg (fun p : (i : I) × accepted i => p.2.val) he
  have hc := Nat.card_le_card_of_injective encode hinj
  simpa only [Nat.card_sigma,Nat.card_eq_fintype_card,
    Fintype.card_sigma,Fintype.card_coe] using hc

theorem pointFibre_card_le_sum [IsSimpleGroup Model]
    {I : Type} [Fintype I] (accepted : I → Finset (Equiv.Perm (Fin 23)))
    (hcover : ∀ f : pointFibre 0, ∃ i : I, image f ∈ accepted i) :
    Nat.card (pointFibre 0) ≤ ∑ i : I, (accepted i).card :=
  card_le_sum_of_injective (fun f => f) (fun _ _ he => he) accepted hcover

/-- A genuine subfibre specified by the first address of the original chart.
Its definition needs no classification or natural-action extension. -/
def firstPointFibre (i : First) : Type :=
  {f : pointFibre 0 // ∃ c : Code, (decodeAtZero c).val = image f ∧ c.1.1 = i}

theorem firstPointFibre_card_le_whitelist_sum [IsSimpleGroup Model]
    (i : First) (failure : Second → Selector) (whitelist : Second → List RawTail)
    (hbatch : ∀ j : Second, batchCheck i.val.val j.val.val (failure j) (whitelist j) = true) :
    Nat.card (firstPointFibre i) ≤ ∑ j : Second, (whitelist j).length := by
  have hcover : ∀ f : firstPointFibre i, ∃ j : Second,
      image f.val ∈ acceptedElements i j (whitelist j) := by
    intro f
    obtain ⟨c,hc,hi⟩ := f.property
    refine ⟨c.1.2,?_⟩
    rw [←hc]
    apply accepts_mem_acceptedElements i c.1.2 (failure c.1.2) (whitelist c.1.2)
      (hbatch c.1.2) c hi rfl
    rw [hc]
    exact CFSGMathieuTwentyThreeProductNecessaryRelations.accepts_of_fixed_product f.val.val
  calc
    Nat.card (firstPointFibre i) ≤ ∑ j : Second, (acceptedElements i j (whitelist j)).card :=
      card_le_sum_of_injective (fun f : firstPointFibre i => f.val) Subtype.val_injective
        (fun j => acceptedElements i j (whitelist j)) hcover
    _ ≤ ∑ j : Second, (whitelist j).length :=
      Finset.sum_le_sum (fun j _ => acceptedElements_card_le_length i j (whitelist j))

theorem pointFibre_card_le_whitelist_sum [IsSimpleGroup Model]
    (failure : First → Second → Selector) (whitelist : First → Second → List RawTail)
    (hbatch : ∀ (i : First) (j : Second),
      batchCheck i.val.val j.val.val (failure i j) (whitelist i j) = true) :
    Nat.card (pointFibre 0) ≤ ∑ i : First, ∑ j : Second, (whitelist i j).length := by
  have hcover : ∀ f : pointFibre 0, ∃ p : Prefix,
      image f ∈ acceptedElements p.1 p.2 (whitelist p.1 p.2) := by
    intro f
    obtain ⟨c,hc⟩ := pointFibre_image_has_code f
    refine ⟨(c.1.1,c.1.2),?_⟩
    exact pointFibre_image_mem_acceptedElements c.1.1 c.1.2
      (failure c.1.1 c.1.2) (whitelist c.1.1 c.1.2) (hbatch c.1.1 c.1.2) f c hc rfl rfl
  have hsum : Nat.card (pointFibre 0) ≤ ∑ p : Prefix, (whitelist p.1 p.2).length := by
    calc
      Nat.card (pointFibre 0) ≤
          ∑ p : Prefix, (acceptedElements p.1 p.2 (whitelist p.1 p.2)).card :=
        pointFibre_card_le_sum (fun p : Prefix => acceptedElements p.1 p.2 (whitelist p.1 p.2)) hcover
      _ ≤ ∑ p : Prefix, (whitelist p.1 p.2).length :=
        Finset.sum_le_sum (fun p _ => acceptedElements_card_le_length p.1 p.2 (whitelist p.1 p.2))
  simpa only [Prefix,Fintype.sum_prod_type] using hsum

theorem three_mul_outer_card_le_twice_whitelist_sum [Finite Model] [IsSimpleGroup Model]
    (hnon : ¬ IsMulCommutative Model)
    (failure : First → Second → Selector) (whitelist : First → Second → List RawTail)
    (hbatch : ∀ (i : First) (j : Second),
      batchCheck i.val.val j.val.val (failure i j) (whitelist i j) = true) :
    3 * Nat.card (PrimitiveSocleRawStructure.Outer Model) ≤
      2 * (∑ i : First, ∑ j : Second, (whitelist i j).length) :=
  (three_mul_outer_card_le_twice_pointFibre hnon).trans
    (Nat.mul_le_mul_left 2 (pointFibre_card_le_whitelist_sum failure whitelist hbatch))

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeIndexedPointFibreCapacity
