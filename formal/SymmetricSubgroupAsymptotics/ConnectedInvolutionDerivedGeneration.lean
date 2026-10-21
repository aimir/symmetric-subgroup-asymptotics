import SymmetricSubgroupAsymptotics.CFSGFiniteFamilyGeneration
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic.Group

/-! Ordinary generation of the actual derived subgroup of a group generated
by involutions. The connected order-three relations make all generators
equal in abelianization. The n-1 displayed even products then generate the
derived subgroup itself, not merely its normal closure. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGeneration
universe u v w

theorem generators_card_le_of_surjective {G : Type u} {H : Type v}
    [Group G] [Group H] (f : G →* H) (hf : Function.Surjective f) {d : ℕ}
    (hG : ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ S.card ≤ d) :
    ∃ S : Finset H, Subgroup.closure (S : Set H) = ⊤ ∧ S.card ≤ d := by
  obtain ⟨S, hS, hcard⟩ := hG
  refine ⟨S.image f, ?_, Finset.card_image_le.trans hcard⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hS]
  exact Subgroup.map_top_of_surjective f hf

theorem generators_card_le_of_family {G : Type u} [Group G]
    {ι : Type v} [Finite ι] (g : ι → G)
    (hgen : Subgroup.closure (Set.range g) = ⊤) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ S.card ≤ Nat.card ι := by
  letI involutionGeneration_indexFintype : Fintype ι := Fintype.ofFinite ι
  let S : Finset G := Finset.univ.image g
  have hs : (S : Set G) = Set.range g := by
    ext x
    simp only [S, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  refine ⟨S, ?_, Finset.card_image_le.trans ?_⟩
  · rw [hs]
    exact hgen
  · simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using
      (le_rfl : Fintype.card ι ≤ Fintype.card ι)

def involutionEvenProducts {G : Type u} [Group G] {ι : Type v}
    (g : ι → G) (base : ι) : Subgroup G :=
  Subgroup.closure (Set.range (fun i : {i : ι // i ≠ base} => g base * g i.val))

theorem involution_even_product_mem {G : Type u} [Group G] {ι : Type v}
    (g : ι → G) (base : ι) (hbase : g base * g base = 1) (i : ι) :
    g base * g i ∈ involutionEvenProducts g base := by
  by_cases hi : i = base
  · subst i
    rw [hbase]
    exact (involutionEvenProducts g base).one_mem
  · change g base * g i ∈ Subgroup.closure
      (Set.range (fun j : {j : ι // j ≠ base} => g base * g j.val))
    exact Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩

theorem involution_even_products_normal {G : Type u} [Group G] {ι : Type v}
    (g : ι → G) (base : ι)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hsq : ∀ i, g i * g i = 1) : (involutionEvenProducts g base).Normal := by
  let H := involutionEvenProducts g base
  let r := g base
  have hr : r * r = 1 := hsq base
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr
  have hconj : ∀ z ∈ H, r * z * r⁻¹ ∈ H := by
    have hm : H.map (MulAut.conj r).toMonoidHom ≤ H := by
      change (Subgroup.closure _).map (MulAut.conj r).toMonoidHom ≤ H
      rw [MonoidHom.map_closure]
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      change r * (r * g i.val) * r⁻¹ ∈ H
      have he : r * (r * g i.val) * r⁻¹ = (r * g i.val)⁻¹ := by
        calc
          _ = (r * r) * g i.val * r⁻¹ := by group
          _ = g i.val * r := by rw [hr, one_mul, hrinv]
          _ = (r * g i.val)⁻¹ := by
            rw [mul_inv_rev, hrinv, inv_eq_of_mul_eq_one_right (hsq i.val)]
      rw [he]
      exact H.inv_mem (involution_even_product_mem g base hr i.val)
    intro z hz
    exact hm ⟨z, hz, rfl⟩
  have hrnorm : r ∈ Subgroup.normalizer H := by
    apply Subgroup.mem_normalizer_iff.mpr
    intro z
    constructor
    · exact hconj z
    · intro hz
      have hh := hconj _ hz
      have he : r * (r * z * r⁻¹) * r⁻¹ = z := by
        calc
          _ = (r * r) * z * (r * r)⁻¹ := by group
          _ = z := by rw [hr]; simp only [one_mul, inv_one, mul_one]
      rwa [he] at hh
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  have hmem : g base * g i ∈ H := involution_even_product_mem g base hr i
  have hnorm : g base * g i ∈ Subgroup.normalizer H := H.le_normalizer hmem
  let rN : Subgroup.normalizer (H : Set G) := ⟨r, hrnorm⟩
  let aN : Subgroup.normalizer (H : Set G) := ⟨g base * g i, hnorm⟩
  have hi := (rN * aN).property
  change r * (g base * g i) ∈ Subgroup.normalizer (H : Set G) at hi
  have he : r * (g base * g i) = g i := by
    change g base * (g base * g i) = g i
    rw [← mul_assoc, hsq base, one_mul]
  rw [he] at hi
  exact hi

theorem commutator_eq_involution_even_products {G : Type u} [Group G] {ι : Type v}
    (g : ι → G) (base : ι)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hsq : ∀ i, g i * g i = 1)
    (hsame : ∀ i, Abelianization.of (g i) = Abelianization.of (g base)) :
    commutator G = involutionEvenProducts g base := by
  let H := involutionEvenProducts g base
  letI involutionGeneration_evenNormal : H.Normal :=
    involution_even_products_normal g base hgen hsq
  have hH : H ≤ commutator G := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    rw [← Abelianization.ker_of G]
    change Abelianization.of (g base * g i.val) = 1
    rw [map_mul, hsame i.val, ← map_mul, hsq base, map_one]
  have hsup : H ⊔ Subgroup.zpowers (g base) = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    have hrmem : g base ∈ H ⊔ Subgroup.zpowers (g base) :=
      (show Subgroup.zpowers (g base) ≤ H ⊔ Subgroup.zpowers (g base) from le_sup_right)
        (Subgroup.mem_zpowers (g base))
    have hprod : g base * g i ∈ H ⊔ Subgroup.zpowers (g base) :=
      (show H ≤ H ⊔ Subgroup.zpowers (g base) from le_sup_left)
        (involution_even_product_mem g base (hsq base) i)
    have hi := (H ⊔ Subgroup.zpowers (g base)).mul_mem hrmem hprod
    simpa only [← mul_assoc, hsq, one_mul] using hi
  exact le_antisymm
    (Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance) hH

theorem involution_derived_generators {G : Type u} [Group G]
    {ι : Type v} [Finite ι] (g : ι → G) (base : ι)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hsq : ∀ i, g i * g i = 1)
    (hsame : ∀ i, Abelianization.of (g i) = Abelianization.of (g base)) :
    ∃ S : Finset (commutator G),
      Subgroup.closure (S : Set (commutator G)) = ⊤ ∧ S.card ≤ Nat.card ι - 1 := by
  letI involutionGeneration_finiteIndex : Fintype ι := Fintype.ofFinite ι
  let a : {i : ι // i ≠ base} → G := fun i => g base * g i.val
  have hc : Nat.card {i : ι // i ≠ base} = Nat.card ι - 1 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq]
  have he : Subgroup.closure (Set.range a) = commutator G :=
    (commutator_eq_involution_even_products g base hgen hsq hsame).symm
  let e : Subgroup.closure (Set.range a) ≃* commutator G := MulEquiv.subgroupCongr he
  apply generators_card_le_of_surjective e.toMonoidHom e.surjective
  rw [← hc]
  exact generators_card_le_of_family (closureGenerators a) (closureGenerators_full a)

theorem commutative_involutions_eq_of_product_cube {A : Type w} [CommGroup A]
    (a b : A) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : (a * b) ^ 3 = 1) : a = b := by
  have h2 : (a * b) ^ 2 = 1 := by rw [mul_pow, ha, hb, mul_one]
  have hp : a * b = 1 := by
    have h3 : (a * b) ^ 2 * (a * b) = 1 := by simpa only [pow_succ] using hab
    rwa [h2, one_mul] at h3
  calc
    a = a * 1 := (mul_one a).symm
    _ = a * (a * b) := by rw [hp]
    _ = b := by rw [← mul_assoc, ← pow_two, ha, one_mul]

theorem connected_involution_derived_generators {G : Type u} [Group G]
    {ι : Type v} [Finite ι] (g : ι → G) (base : ι)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hsq : ∀ i, g i ^ 2 = 1) (R : ι → ι → Prop)
    (hedge : ∀ i j, R i j → (g i * g j) ^ 3 = 1)
    (hconn : ∀ i, Relation.ReflTransGen R base i) :
    ∃ S : Finset (commutator G),
      Subgroup.closure (S : Set (commutator G)) = ⊤ ∧ S.card ≤ Nat.card ι - 1 := by
  have heq : ∀ i j, R i j → Abelianization.of (g i) = Abelianization.of (g j) := by
    intro i j hij
    apply commutative_involutions_eq_of_product_cube
    · simp only [← map_pow, hsq, map_one]
    · simp only [← map_pow, hsq, map_one]
    · simp only [← map_mul, ← map_pow, hedge i j hij, map_one]
  have hpath : ∀ {i j}, Relation.ReflTransGen R i j →
      Abelianization.of (g i) = Abelianization.of (g j) := by
    intro i j h
    induction h with
    | refl => rfl
    | tail _ hij ih => exact ih.trans (heq _ _ hij)
  exact involution_derived_generators g base hgen
    (fun i => by simpa only [pow_two] using hsq i)
    (fun i => (hpath (hconn i)).symm)

end SymmetricSubgroupAsymptotics.CFSGGeneration
