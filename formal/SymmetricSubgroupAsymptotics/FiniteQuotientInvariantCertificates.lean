import SymmetricSubgroupAsymptotics.PrimeRelativeHeadChainCapacity
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! Finite generator tests for invariants of the actual quotient G/N.
The center is counted through its original preimage; the derived group is
the image of the original derived group. No abstract target group is used. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

variable {G ι : Type*} [Group G]

/-- Commuting with every member of a generating tuple is an exact center test. -/
theorem mem_center_iff_generator_commute
    (generators : ι → G) (hgen : Subgroup.closure (Set.range generators)=⊤)
    (x : G) :
    x ∈ Subgroup.center G ↔ ∀ i, x * generators i=generators i * x := by
  constructor
  · intro hx i
    exact (Subgroup.mem_center_iff.mp hx (generators i)).symm
  · intro hx
    have hle : Subgroup.closure (Set.range generators) ≤ Subgroup.centralizer {x} := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨i,rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hx i).symm
    apply Subgroup.mem_center_iff.mpr
    intro y
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (hle (show y ∈ Subgroup.closure (Set.range generators) by rw [hgen]; trivial))

variable (N : Subgroup G) [N.Normal]

/-- The quotient images of the same original generators generate the actual quotient. -/
theorem quotient_generators_full
    (generators : ι → G) (hgen : Subgroup.closure (Set.range generators)=⊤) :
    Subgroup.closure (Set.range (fun i => QuotientGroup.mk' N (generators i)))=⊤ := by
  have h := congrArg (fun S : Subgroup G => S.map (QuotientGroup.mk' N)) hgen
  dsimp only at h
  rw [MonoidHom.map_closure,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h
  have hs : (QuotientGroup.mk' N) '' Set.range generators =
      Set.range (fun i => QuotientGroup.mk' N (generators i)) := by
    ext y
    simp
  rwa [hs] at h

/-- The literal original preimage of the center of G/N. -/
def quotientCenterPreimage : Subgroup G :=
  (Subgroup.center (G ⧸ N)).comap (QuotientGroup.mk' N)

instance quotientCenterPreimage_normal : (quotientCenterPreimage N).Normal :=
  Subgroup.Normal.comap inferInstance _

theorem le_quotientCenterPreimage : N ≤ quotientCenterPreimage N := by
  intro x hx
  change QuotientGroup.mk' N x ∈ Subgroup.center (G ⧸ N)
  have he : QuotientGroup.mk' N x=1 := (QuotientGroup.eq_one_iff (N := N) x).mpr hx
  rw [he]
  exact (Subgroup.center _).one_mem

/-- A finite test using the original tuple and membership in the original N. -/
theorem mem_quotientCenterPreimage_iff
    (generators : ι → G) (hgen : Subgroup.closure (Set.range generators)=⊤)
    (x : G) :
    x ∈ quotientCenterPreimage N ↔ ∀ i, ⁅x,generators i⁆ ∈ N := by
  change QuotientGroup.mk' N x ∈ Subgroup.center (G ⧸ N) ↔ _
  rw [mem_center_iff_generator_commute _ (quotient_generators_full N generators hgen)]
  apply forall_congr'
  intro i
  rw [← commutatorElement_eq_one_iff_mul_comm,← map_commutatorElement]
  exact QuotientGroup.eq_one_iff (N := N) _

/-- Exact cardinality of the actual quotient center, from its original preimage. -/
theorem quotientCenter_card_mul [Finite G] :
    Nat.card (Subgroup.center (G ⧸ N)) * Nat.card N =
      Nat.card (quotientCenterPreimage N) := by
  have he : normalChainQuotient N (quotientCenterPreimage N)=
      Subgroup.center (G ⧸ N) := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hx
    · intro hy
      obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective N y
      exact ⟨x,hy,rfl⟩
  have hc := normalChainQuotient_card_mul N (quotientCenterPreimage N)
    (le_quotientCenterPreimage N)
  rwa [he] at hc

/-- A normal subgroup containing all generator-pair commutators contains
the entire original derived subgroup. Only the finite tuple is tested. -/
theorem commutator_le_of_generator_commutators
    (generators : ι → G) (hgen : Subgroup.closure (Set.range generators)=⊤)
    (hcomm : ∀ i j, ⁅generators i,generators j⁆ ∈ N) :
    commutator G ≤ N := by
  let q := QuotientGroup.mk' N
  let S := Set.range (fun i => q (generators i))
  have hS : Subgroup.closure S=⊤ := quotient_generators_full N generators hgen
  have hpair : ∀ x ∈ S, ∀ y ∈ S, x*y=y*x := by
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff (N := N) _).mpr (hcomm i j)
  letI : IsMulCommutative (Subgroup.closure S) :=
    Subgroup.isMulCommutative_closure hpair
  have hQ (x y : G ⧸ N) : x*y=y*x := by
    have hx : x ∈ Subgroup.closure S := by rw [hS]; trivial
    have hy : y ∈ Subgroup.closure S := by rw [hS]; trivial
    exact congrArg Subtype.val
      (mul_comm' (⟨x,hx⟩ : Subgroup.closure S) ⟨y,hy⟩)
  rw [commutator_eq_closure]
  apply (Subgroup.closure_le N).mpr
  rintro _ ⟨x,y,rfl⟩
  apply (QuotientGroup.eq_one_iff (N := N) _).mp
  change q ⁅x,y⁆=1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (hQ _ _)

/-- Derived cardinality in the same original quotient when N is contained
in the original derived subgroup. This is an identity, not a rank premise. -/
theorem quotientCommutator_card_mul [Finite G] (hN : N ≤ commutator G) :
    Nat.card (commutator (G ⧸ N)) * Nat.card N = Nat.card (commutator G) := by
  have he : normalChainQuotient N (commutator G)=commutator (G ⧸ N) := by
    rw [normalChainQuotient,map_commutator_eq,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)]
    rfl
  have hc := normalChainQuotient_card_mul N (commutator G) hN
  rwa [he] at hc

end SymmetricSubgroupAsymptotics
