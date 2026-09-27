import Mathlib.GroupTheory.GroupAction.CardCommute
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! The class-count extension inequality for an actual finite group and
an actual normal subgroup. Conjugation by N on one original quotient
coset has at most k(N) orbits, by Burnside and a fixed-point injection into
an original centralizer. Those orbits cover the conjugacy classes above
one quotient class. No splitting or class-count hypothesis is used.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics

namespace ConjugacyClassExtension

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal]

/-- One literal fibre of the original quotient homomorphism. -/
abbrev NormalCoset (q : G ⧸ N) :=
  {g : G // QuotientGroup.mk' N g = q}

/-- N acts on each quotient coset by original conjugation. -/
instance normalCosetConjugation (q : G ⧸ N) : MulAction N (NormalCoset N q) where
  smul a x := ⟨(a : G)*x.1*(a : G)⁻¹, by
    have ha : QuotientGroup.mk' N (a : G) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr a.2
    simp only [map_mul, map_inv, ha, one_mul, inv_one, mul_one]
    exact x.2⟩
  one_smul x := by
    apply Subtype.ext
    change ((1 : N) : G)*x.1*((1 : N) : G)⁻¹ = x.1
    simp
  mul_smul a b x := by
    apply Subtype.ext
    change ((a*b : N) : G)*x.1*((a*b : N) : G)⁻¹ =
      (a : G)*((b : G)*x.1*(b : G)⁻¹)*(a : G)⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev, mul_assoc]

private theorem coset_ratio_mem (q : G ⧸ N) (x y : NormalCoset N q) :
    x.1*y.1⁻¹ ∈ N := by
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' N (x.1*y.1⁻¹) = 1
  simp only [map_mul, map_inv, x.2, y.2, mul_inv_cancel]

private theorem fixed_commute (q : G ⧸ N) (a : N)
    (x : MulAction.fixedBy (NormalCoset N q) a) :
    Commute (a : G) x.1.1 := by
  have hx := congrArg (fun y : NormalCoset N q => y.1) x.2
  change (a : G)*x.1.1*(a : G)⁻¹ = x.1.1 at hx
  exact mul_inv_eq_iff_eq_mul.mp hx

/-- Divide by a fixed coset element to obtain an original element of N
centralizing a. Only injectivity, not any canonical choice, is needed. -/
private def fixedRatio (q : G ⧸ N) (a : N)
    (y : MulAction.fixedBy (NormalCoset N q) a) :
    MulAction.fixedBy (NormalCoset N q) a → {b : N // Commute a b} :=
  fun x => ⟨⟨x.1.1*y.1.1⁻¹, coset_ratio_mem N q x.1 y.1⟩, by
    change a * (⟨x.1.1*y.1.1⁻¹, coset_ratio_mem N q x.1 y.1⟩ : N) =
      (⟨x.1.1*y.1.1⁻¹, coset_ratio_mem N q x.1 y.1⟩ : N) * a
    apply Subtype.ext
    exact ((fixed_commute N q a x).mul_right
      (Commute.inv_right (fixed_commute N q a y))).eq⟩

private theorem fixedRatio_injective (q : G ⧸ N) (a : N)
    (y : MulAction.fixedBy (NormalCoset N q) a) :
    Function.Injective (fixedRatio N q a y) := by
  intro x z h
  have hv := congrArg (fun t : {b : N // Commute a b} => (t.1 : G)) h
  change x.1.1*y.1.1⁻¹ = z.1.1*y.1.1⁻¹ at hv
  apply Subtype.ext
  apply Subtype.ext
  exact mul_right_cancel hv

private theorem fixed_card_le [Finite G] (q : G ⧸ N) (a : N) :
    Nat.card (MulAction.fixedBy (NormalCoset N q) a) ≤
      Nat.card {b : N // Commute a b} := by
  rcases isEmpty_or_nonempty (MulAction.fixedBy (NormalCoset N q) a) with he | he
  · letI := he
    simp only [Nat.card_of_isEmpty, Nat.zero_le]
  · let y := Classical.choice he
    exact Nat.card_le_card_of_injective (fixedRatio N q a y)
      (fixedRatio_injective N q a y)

/-- Conjugation by the original N on one quotient coset has at most
as many orbits as N has conjugacy classes. -/
theorem normalCoset_orbit_card_le [Finite G] (q : G ⧸ N) :
    Nat.card (MulAction.orbitRel.Quotient N (NormalCoset N q)) ≤
      Nat.card (ConjClasses N) := by
  letI : Fintype N := Fintype.ofFinite _
  have hburn :
      (∑ a : N, Nat.card (MulAction.fixedBy (NormalCoset N q) a)) =
        Nat.card (MulAction.orbitRel.Quotient N (NormalCoset N q))*Nat.card N := by
    rw [← Nat.card_sigma,
      Nat.card_congr (MulAction.sigmaFixedByEquivOrbitsProdGroup N (NormalCoset N q)),
      Nat.card_prod]
  have hcomm : (∑ a : N, Nat.card {b : N // Commute a b}) =
      Nat.card (ConjClasses N)*Nat.card N := by
    calc
      _ = Nat.card ((a : N) × {b : N // Commute a b}) := (Nat.card_sigma).symm
      _ = Nat.card {p : N × N // Commute p.1 p.2} :=
        (Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
          (fun a b : N => Commute a b))).symm
      _ = _ := card_comm_eq_card_conjClasses_mul_card N
  have hmul :
      Nat.card (MulAction.orbitRel.Quotient N (NormalCoset N q))*Nat.card N ≤
        Nat.card (ConjClasses N)*Nat.card N := by
    rw [← hburn, ← hcomm]
    exact Finset.sum_le_sum (fun a _ => fixed_card_le N q a)
  exact Nat.le_of_mul_le_mul_right hmul (Nat.card_pos (α := N))

/-- The exact fibre of the original quotient map on conjugacy classes. -/
abbrev ClassFiber (q : ConjClasses (G ⧸ N)) :=
  {c : ConjClasses G // ConjClasses.map (QuotientGroup.mk' N) c = q}

private def cosetClassMap (q : G ⧸ N) :
    MulAction.orbitRel.Quotient N (NormalCoset N q) →
      ClassFiber N (ConjClasses.mk q) :=
  Quotient.lift
    (fun x : NormalCoset N q => ⟨ConjClasses.mk x.1, by
      change ConjClasses.mk (QuotientGroup.mk' N x.1) = ConjClasses.mk q
      rw [x.2]⟩)
    (by
      intro x y hxy
      apply Subtype.ext
      apply ConjClasses.mk_eq_mk_iff_isConj.mpr
      change x ∈ MulAction.orbit N y at hxy
      obtain ⟨a, ha⟩ := hxy
      have hv := congrArg (fun z : NormalCoset N q => z.1) ha
      change (a : G)*y.1*(a : G)⁻¹ = x.1 at hv
      exact (isConj_iff.mpr ⟨(a : G), hv⟩).symm)

private theorem cosetClassMap_surjective (q : G ⧸ N) :
    Function.Surjective (cosetClassMap N q) := by
  intro c
  obtain ⟨g, hg⟩ := ConjClasses.exists_rep c.1
  have hq : ConjClasses.mk (QuotientGroup.mk' N g) = ConjClasses.mk q := by
    change ConjClasses.map (QuotientGroup.mk' N) (ConjClasses.mk g) = _
    rw [hg]
    exact c.2
  obtain ⟨t, ht⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hq)
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective N t
  let y : G := a*g*a⁻¹
  have hy : QuotientGroup.mk' N y = q := by
    dsimp only [y]
    rw [map_mul, map_mul, map_inv, ha]
    exact ht
  refine ⟨Quotient.mk'' (⟨y, hy⟩ : NormalCoset N q), ?_⟩
  apply Subtype.ext
  change ConjClasses.mk y = c.1
  have hgy : ConjClasses.mk g = ConjClasses.mk y :=
    ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨a, rfl⟩)
  exact hgy.symm.trans hg

end ConjugacyClassExtension

variable {G : Type*} [Group G] [Finite G]

/-- Every fibre of the actual quotient homomorphism on conjugacy classes
has cardinal at most the number of conjugacy classes of the original N. -/
theorem conjugacyClass_quotient_fiber_card_le (N : Subgroup G) [N.Normal]
    (q : ConjClasses (G ⧸ N)) :
    Nat.card {c : ConjClasses G //
      ConjClasses.map (QuotientGroup.mk' N) c = q} ≤ Nat.card (ConjClasses N) := by
  obtain ⟨q, rfl⟩ := ConjClasses.exists_rep q
  exact (Nat.card_le_card_of_surjective (ConjugacyClassExtension.cosetClassMap N q)
    (ConjugacyClassExtension.cosetClassMap_surjective N q)).trans
      (ConjugacyClassExtension.normalCoset_orbit_card_le N q)

/-- The class-count extension inequality for an actual finite group and
its original normal subgroup. No additional class bound is a premise. -/
theorem conjugacyClass_card_le_normal_mul_quotient (N : Subgroup G) [N.Normal] :
    Nat.card (ConjClasses G) ≤
      Nat.card (ConjClasses N)*Nat.card (ConjClasses (G ⧸ N)) := by
  letI : Fintype (ConjClasses (G ⧸ N)) := Fintype.ofFinite _
  calc
    _ = Nat.card ((q : ConjClasses (G ⧸ N)) ×
        {c : ConjClasses G // ConjClasses.map (QuotientGroup.mk' N) c = q}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv
        (ConjClasses.map (QuotientGroup.mk' N)))).symm
    _ = ∑ q : ConjClasses (G ⧸ N), Nat.card {c : ConjClasses G //
        ConjClasses.map (QuotientGroup.mk' N) c = q} := Nat.card_sigma
    _ ≤ ∑ _q : ConjClasses (G ⧸ N), Nat.card (ConjClasses N) :=
      Finset.sum_le_sum (fun q _ => conjugacyClass_quotient_fiber_card_le N q)
    _ = Fintype.card (ConjClasses (G ⧸ N))*Nat.card (ConjClasses N) := by simp
    _ = _ := by rw [← Nat.card_eq_fintype_card]; exact Nat.mul_comm _ _

end SymmetricSubgroupAsymptotics

end
