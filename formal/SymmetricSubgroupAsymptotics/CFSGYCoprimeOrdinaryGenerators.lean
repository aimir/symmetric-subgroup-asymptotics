import SymmetricSubgroupAsymptotics.CFSGYCoprimeArmGeneration
import SymmetricSubgroupAsymptotics.DerivedNormalizedInvolutionFamily
import SymmetricSubgroupAsymptotics.PrimitiveSocleYSectionOrdinaryTail
import Mathlib.Data.Fintype.Option

/-! Genuine compressed ordinary generating families for the four pinned
Y models. Actual arm periods3/4/5 and cross-arm commutation recover the
original source from three/two/three/three displayed full-group elements.
The SAME families normalize into the actual derived subgroup and descend
through its FULL centre quotient, giving heads4/2/4/4. No finite-order,
model identification, simple-generation or outer-bound premise occurs. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGYCoprimeOrdinaryGenerators
open CFSG.Models.YGroups CFSGGeneration CFSGReduction
open CFSGYArmProductGeneration CFSGYArmProductPeriods CFSGYCoprimeArmGeneration

/-- A proved package of literal source, derived and FULL quotient families.
It is an OUTPUT of the model theorems, never a supplied generator premise. -/
structure GenerationBounds (arms : Arms) (original derived : ℕ) : Prop where
  originalFamily : ∃ S : Finset (CFSG.Models.YGroups.Group arms),
    Subgroup.closure (S : Set (CFSG.Models.YGroups.Group arms)) = ⊤ ∧ S.card ≤ original
  derivedFamily : ∃ S : Finset (commutator (CFSG.Models.YGroups.Group arms)),
    Subgroup.closure (S : Set (commutator (CFSG.Models.YGroups.Group arms))) = ⊤ ∧ S.card ≤ derived
  fullCentralQuotientFamily : ∃ S : Finset (SimpleSection arms),
    Subgroup.closure (S : Set (SimpleSection arms)) = ⊤ ∧ S.card ≤ derived

private abbrev centralGenerator (arms : Arms) : CFSG.Models.YGroups.Group arms :=
  PresentedGroup.of (rels := relations arms) none

private theorem abelianization_arm_product (arms : Arms) (i : Fin 3) :
    Abelianization.of (armProduct arms i) =
      (Abelianization.of (centralGenerator arms))^(arms.length i) := by
  rw [armProduct,armList,map_list_prod,List.map_ofFn]
  change (List.ofFn (fun d : Fin (arms.length i) =>
    Abelianization.of (PresentedGroup.of (rels := relations arms) (some ⟨i,d⟩)))).prod = _
  simp only [y_abelianization_generators_equal,List.ofFn_const,List.prod_replicate]

private theorem original_family {G ι : Type*} [Group G] [Finite ι]
    (f : ι → G) (r : G) (hgen : Subgroup.closure (Set.range f ∪ {r}) = ⊤) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ S.card ≤ Nat.card ι+1 := by
  let w : Option ι → G := fun a => match a with | none => r | some i => f i
  have hw : Set.range w = Set.range f ∪ {r} := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      cases a with
      | none => exact Or.inr rfl
      | some i => exact Or.inl ⟨i,rfl⟩
    · intro hx
      rcases hx with ⟨i,rfl⟩ | hx
      · exact ⟨some i,rfl⟩
      · have hx : x = r := hx
        subst x
        exact ⟨none,rfl⟩
  have hfull : Subgroup.closure (Set.range w) = ⊤ := by rw [hw]; exact hgen
  obtain ⟨S,hS,hcard⟩ := generators_card_le_of_family w hfull
  letI : Fintype ι := Fintype.ofFinite _
  have hc : Nat.card (Option ι) = Nat.card ι+1 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_option,← Nat.card_eq_fintype_card]
  exact ⟨S,hS,by simpa only [hc] using hcard⟩

private theorem bounds_of_family {ι : Type} [Finite ι] (arms : Arms)
    (f : ι → CFSG.Models.YGroups.Group arms) (length : ι → ℕ)
    (hA : ∀ i, Abelianization.of (f i) = (Abelianization.of (centralGenerator arms))^(length i))
    (hgen : Subgroup.closure (Set.range f ∪ {centralGenerator arms}) = ⊤) :
    GenerationBounds arms (Nat.card ι+1) (2*Nat.card ι) := by
  have hD := DerivedNormalizedInvolutionFamily.exists_generating_finset f
    (centralGenerator arms) length (y_generator_sq arms none) hA hgen
  have hQ := generators_card_le_of_surjective
    (QuotientGroup.mk' (Subgroup.center (commutator (CFSG.Models.YGroups.Group arms))))
    (QuotientGroup.mk'_surjective _) hD
  exact ⟨original_family f (centralGenerator arms) hgen,hD,hQ⟩

private theorem paired_bounds (arms : Arms) (i j k : Fin 3) (hij : i ≠ j)
    (hcover : ∀ a : Fin 3, a = i ∨ a = j ∨ a = k)
    (m n : ℕ) (hcop : m.Coprime n)
    (hi : (armProduct arms i)^m = 1) (hj : (armProduct arms j)^n = 1) :
    GenerationBounds arms 3 4 := by
  let length : Fin 2 → ℕ := ![arms.length i+arms.length j,arms.length k]
  have hA : ∀ a, Abelianization.of (pairedArms arms i j k a) =
      (Abelianization.of (centralGenerator arms))^(length a) := by
    intro a
    fin_cases a
    · change Abelianization.of (armProduct arms i*armProduct arms j) =
        (Abelianization.of (centralGenerator arms))^(arms.length i+arms.length j)
      rw [map_mul,abelianization_arm_product,abelianization_arm_product,pow_add]
    · exact abelianization_arm_product arms k
  have h := bounds_of_family arms (pairedArms arms i j k) length hA
    (paired_arms_generate arms i j k hij hcover m n hcop hi hj)
  simpa only [Nat.card_fin] using h

private theorem all_bounds (arms : Arms) (m n k : ℕ)
    (hcop : m.Coprime n) (hcopLast : (m*n).Coprime k)
    (h0 : (armProduct arms 0)^m = 1) (h1 : (armProduct arms 1)^n = 1)
    (h2 : (armProduct arms 2)^k = 1) : GenerationBounds arms 2 2 := by
  let length : Fin 1 → ℕ := fun _ => arms.length 0+arms.length 1+arms.length 2
  have hA : ∀ a, Abelianization.of (allArms arms a) =
      (Abelianization.of (centralGenerator arms))^(length a) := by
    intro a
    change Abelianization.of (armProduct arms 0*armProduct arms 1*armProduct arms 2) = _
    rw [map_mul,map_mul,abelianization_arm_product,abelianization_arm_product,
      abelianization_arm_product]
    simp only [length,pow_add]
  have h := bounds_of_family arms (allArms arms) length hA
    (all_arms_generate arms m n k hcop hcopLast h0 h1 h2)
  simpa only [Nat.card_fin] using h

/-- Original Y332 head3; actual derived and full-centre Fi22 heads4. -/
theorem fischer22_bounds : GenerationBounds arms332 3 4 := by
  exact paired_bounds arms332 0 2 1 (by decide)
    (by intro a; fin_cases a <;> simp) 4 3 (by decide)
    (arm_product_period_four arms332 0 (by decide))
    (arm_product_period_three arms332 2 (by decide))

/-- The actual arm periods5,4,3 are pairwise coprime, yielding a displayed
whole-group pair and a derived/full-centre Fischer23 pair. -/
theorem fischer23_bounds : GenerationBounds arms432 2 2 := by
  exact all_bounds arms432 5 4 3 (by decide) (by decide)
    (arm_product_period_five arms432 0 (by decide))
    (arm_product_period_four arms432 1 (by decide))
    (arm_product_period_three arms432 2 (by decide))

/-- Original Y442 head3; actual derived and full-centre Fi24prime heads4. -/
theorem fischer24Prime_bounds : GenerationBounds arms442 3 4 := by
  exact paired_bounds arms442 0 2 1 (by decide)
    (by intro a; fin_cases a <;> simp) 5 3 (by decide)
    (arm_product_period_five arms442 0 (by decide))
    (arm_product_period_three arms442 2 (by decide))

/-- Original Y433 head3; actual derived and full-centre Baby heads4. -/
theorem babyMonster_bounds : GenerationBounds arms433 3 4 := by
  exact paired_bounds arms433 0 1 2 (by decide)
    (by intro a; fin_cases a <;> simp) 5 4 (by decide)
    (arm_product_period_five arms433 0 (by decide))
    (arm_product_period_four arms433 1 (by decide))

/-- ONE family consumer supplies genuine head4 for all four actual pinned
simple models; the stronger Fischer23 head2 remains in its bound package. -/
theorem y_model_generators (s : CFSG.Sporadic)
    (hs : PrimitiveSocleYSectionOrdinaryTail.IsYSectionModel s) :
    ∃ S : Finset s.Model, Subgroup.closure (S : Set s.Model) = ⊤ ∧ S.card ≤ 4 := by
  cases s <;> try { exact False.elim hs }
  case fi22 => exact fischer22_bounds.fullCentralQuotientFamily
  case fi23 =>
    obtain ⟨S,hS,hcard⟩ := fischer23_bounds.fullCentralQuotientFamily
    exact ⟨S,hS,hcard.trans (by decide)⟩
  case fi24Prime => exact fischer24Prime_bounds.fullCentralQuotientFamily
  case babyMonster => exact babyMonster_bounds.fullCentralQuotientFamily

end SymmetricSubgroupAsymptotics.CFSGYCoprimeOrdinaryGenerators
