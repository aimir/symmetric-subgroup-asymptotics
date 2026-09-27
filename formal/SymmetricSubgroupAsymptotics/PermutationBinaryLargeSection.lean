import SymmetricSubgroupAsymptotics.PermutationBinaryOrbitSection
import SymmetricSubgroupAsymptotics.NormalSubgroupOrbitIndex
import SymmetricSubgroupAsymptotics.BinaryZeroCutWideParameters

/-! A section larger than half the original transitive binary permutation
degree has faithful action. The proof uses the actual normal action kernel
and actual orbit quotients; the section is never embedded back into the
permutation module. No equality classification of Boolean-width extremizers
or character-kernel incidence estimate is needed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics

theorem binary_middle_twice_le_power (a : ℕ) (ha : 1≤a) :
    2*a.choose (a/2)≤2^a := by
  induction a, ha using Nat.le_induction with
  | base => decide
  | succ a ha ih =>
    calc
      2*(a+1).choose ((a+1)/2)≤2*(2*a.choose (a/2)) :=
        Nat.mul_le_mul_left 2 (binary_middle_succ_le_twice a)
      _ = 2*(2*a.choose (a/2)) := rfl
      _ ≤ 2*(2^a) := Nat.mul_le_mul_left 2 ih
      _ = 2^(a+1) := by rw [pow_succ]; omega

variable {k G X A : Type} [Field k] [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] [MulAction.IsPretransitive G X]
    [AddCommGroup A] [Module k A] [FiniteDimensional k A]

/-- A nontrivial normal subgroup of the faithful transitive original
group has no singleton orbit on the original points. -/
theorem normal_orbit_card_ne_one_of_ne_bot (K : Subgroup G) [K.Normal]
    (hK : K≠⊥) (x : X) : Nat.card (MulAction.orbit K x)≠1 := by
  intro hx
  apply hK
  apply le_antisymm ?_ bot_le
  intro g hg
  apply Subgroup.mem_bot.mpr
  apply eq_of_smul_eq_smul (α := X)
  intro y
  let o : MulAction.orbitRel.Quotient K X := Quotient.mk'' y
  have hy := (normal_orbit_card_eq K x o).trans hx
  change Nat.card (MulAction.orbit K y)=1 at hy
  have hy' : Fintype.card (MulAction.orbit K y)=1 := by
    simpa only [Fintype.card_eq_nat_card] using hy
  have hfixed := MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mpr hy'
  exact (MulAction.mem_fixedPoints.mp hfixed ⟨g,hg⟩).trans (one_smul G y).symm

/-- If an actual section is trivial under a nontrivial original normal
subgroup, its dimension is at most half the original transitive degree. -/
theorem permutationSection_twice_finrank_le_of_normal_trivial
    (hG : IsPGroup 2 G) (K : Subgroup G) [K.Normal] (hK : K≠⊥) (x : X)
    (M : Subrepresentation (permutationFunctionRepresentation k G X))
    (q : M.toSubmodule →ₗ[k] A) (hq : Function.Surjective q)
    (htrivial : ∀ (g : K) (m : M.toSubmodule),
      q (M.toRepresentation (g:G) m)=q m) :
    2*Module.finrank k A≤Nat.card X := by
  obtain ⟨a,ha⟩ := (hG.to_subgroup K).card_orbit x
  have ha1 : 1≤a := by
    by_contra hn
    have ha0 : a=0 := by omega
    apply normal_orbit_card_ne_one_of_ne_bot K hK x
    simpa only [ha0,pow_zero] using ha
  let MK : Subrepresentation (permutationFunctionRepresentation k K X) := {
    toSubmodule := M.toSubmodule
    apply_mem_toSubmodule := fun g _ hv => M.apply_mem_toSubmodule (g:G) hv }
  have hcard (o : MulAction.orbitRel.Quotient K X) : Nat.card o.orbit=2^a :=
    (normal_orbit_card_eq K x o).trans ha
  have hb := twoGroup_permutation_trivial_quotient_finrank_le_orbit_widths
    (hG.to_subgroup K) (fun _ => a) hcard MK q hq htrivial
  have hb' : Module.finrank k A≤
      Nat.card (MulAction.orbitRel.Quotient K X)*a.choose (a/2) := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      Fintype.card_eq_nat_card] using hb
  have hc := normal_orbit_card_mul_classes K x
  rw [ha] at hc
  calc
    2*Module.finrank k A ≤
        2*(Nat.card (MulAction.orbitRel.Quotient K X)*a.choose (a/2)) :=
      Nat.mul_le_mul_left 2 hb'
    _ = Nat.card (MulAction.orbitRel.Quotient K X)*(2*a.choose (a/2)) := by ring
    _ ≤ Nat.card (MulAction.orbitRel.Quotient K X)*(2^a) :=
      Nat.mul_le_mul_left _ (binary_middle_twice_le_power a ha1)
    _ = Nat.card X := (Nat.mul_comm _ _).trans hc

/-- A large section has faithful action by the SAME original group.
The only section datum is an actual onto intertwiner from an original
permutation subrepresentation. -/
theorem permutationSection_injective_of_half_lt
    (hG : IsPGroup 2 G) (x : X) (ρ : Representation k G A)
    (M : Subrepresentation (permutationFunctionRepresentation k G X))
    (q : M.toRepresentation.IntertwiningMap ρ) (hq : Function.Surjective q)
    (hlarge : Nat.card X<2*Module.finrank k A) : Function.Injective ρ := by
  apply (MonoidHom.ker_eq_bot_iff ρ).mp
  by_contra hker
  have hb := permutationSection_twice_finrank_le_of_normal_trivial hG
    ρ.ker hker x M q.toLinearMap hq (by
      intro g m
      change q (M.toRepresentation (g:G) m)=q m
      rw [Representation.IntertwiningMap.isIntertwining _ _ q]
      have hg : ρ (g:G)=1 := g.property
      rw [hg]
      rfl)
  exact (not_lt_of_ge hb) hlarge

end SymmetricSubgroupAsymptotics
