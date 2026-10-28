import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic

/-! Distinct normalizer translates of the SAME subgroup orbit are
detected by its central point-stabilizer kernel. No transitivity on a
menu of all lines or decomposition of the whole point set is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CentralKernelNormalizerOrbitPacking
open MulAction

variable {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem normalizes_central_kernel_of_orbit_return
    (P Z : Subgroup G) (hZC : Z ≤ Subgroup.centralizer (P : Set G))
    (t : G) (htZ : t ∈ Subgroup.normalizer (Z : Set G)) (x : X)
    (hreturn : t • x ∈ orbit P x) :
    t ∈ Subgroup.normalizer ((Z ⊓ stabilizer G x : Subgroup G) : Set G) := by
  obtain ⟨r, hr⟩ := hreturn
  change (r : G) • x = t • x at hr
  apply Subgroup.mem_normalizer_fintype
  intro w hw
  let c := t * w * t⁻¹
  have hcZ : c ∈ Z := (Subgroup.mem_normalizer_iff.mp htZ w).mp hw.1
  refine ⟨hcZ, ?_⟩
  have hwx : w • x = x := hw.2
  have hct : c • (t • x) = t • x := by
    change (t * w * t⁻¹) • (t • x) = t • x
    simpa only [mul_smul, inv_smul_smul, hwx]
  have hcr : c * (r : G) = (r : G) * c :=
    (Subgroup.mem_centralizer_iff.mp (hZC hcZ) r.val r.property).symm
  have hrf : (r : G) • (c • x) = (r : G) • x := by
    calc
      (r : G) • (c • x) = ((r : G) * c) • x := (mul_smul _ _ _).symm
      _ = (c * (r : G)) • x := by rw [hcr]
      _ = c • ((r : G) • x) := mul_smul _ _ _
      _ = c • (t • x) := by rw [hr]
      _ = t • x := hct
      _ = (r : G) • x := hr.symm
  exact (MulAction.toPerm (r : G)).injective hrf

theorem card_mul_orbit_le (P : Subgroup G) (t : G)
    (htP : t ∈ Subgroup.normalizer (P : Set G)) (x : X) (m : ℕ)
    (hreturn : ∀ k : ℕ, 0 < k → k < m → t ^ k • x ∉ orbit P x) :
    m * Nat.card (orbit P x) ≤ Nat.card X := by
  classical
  let f : Fin m × orbit P x → X := fun z => t ^ z.1.val • z.2.val
  have hcross (i j : Fin m) (hij : i.val < j.val) (u v : orbit P x) :
      t ^ i.val • u.val ≠ t ^ j.val • v.val := by
    intro he
    let d := j.val - i.val
    have hd0 : 0 < d := Nat.sub_pos_of_lt hij
    have hdm : d < m := (Nat.sub_le _ _).trans_lt j.isLt
    have hdiff : u.val = t ^ d • v.val := by
      apply (MulAction.toPerm (t ^ i.val)).injective
      calc
        t ^ i.val • u.val = t ^ j.val • v.val := he
        _ = t ^ i.val • (t ^ d • v.val) := by
          rw [← mul_smul, ← pow_add, Nat.add_sub_of_le hij.le]
    obtain ⟨r, hr⟩ := u.property
    obtain ⟨s, hs⟩ := v.property
    change (r : G) • x = u.val at hr
    change (s : G) • x = v.val at hs
    have hnorm : t ^ d ∈ Subgroup.normalizer (P : Set G) :=
      (Subgroup.normalizer (P : Set G)).pow_mem htP d
    have hq : t ^ d * (s : G)⁻¹ * (t ^ d)⁻¹ * (r : G) ∈ P :=
      P.mul_mem ((Subgroup.mem_normalizer_iff.mp hnorm _).mp (P.inv_mem s.property)) r.property
    apply hreturn d hd0 hdm
    refine ⟨⟨_, hq⟩, ?_⟩
    change (t ^ d * (s : G)⁻¹ * (t ^ d)⁻¹ * (r : G)) • x = t ^ d • x
    rw [mul_smul, mul_smul, mul_smul, hr, hdiff, inv_smul_smul, ← hs, inv_smul_smul]
  have hf : Function.Injective f := by
    rintro ⟨i, u⟩ ⟨j, v⟩ he
    have hij : i = j := by
      apply Fin.ext
      rcases lt_trichotomy i.val j.val with h | h | h
      · exact (hcross i j h u v he).elim
      · exact h
      · exact (hcross j i h v u he.symm).elim
    subst j
    exact Prod.ext rfl (Subtype.ext ((MulAction.toPerm (t ^ i.val)).injective he))
  have h := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_prod, Nat.card_fin] using h

theorem card_mul_orbit_le_of_central_kernel
    (P Z : Subgroup G) (hZC : Z ≤ Subgroup.centralizer (P : Set G))
    (t : G) (htP : t ∈ Subgroup.normalizer (P : Set G))
    (htZ : t ∈ Subgroup.normalizer (Z : Set G)) (x : X) (m : ℕ)
    (hline : ∀ k : ℕ, 0 < k → k < m →
      t ^ k ∉ Subgroup.normalizer ((Z ⊓ stabilizer G x : Subgroup G) : Set G)) :
    m * Nat.card (orbit P x) ≤ Nat.card X := by
  apply card_mul_orbit_le P t htP x m
  intro k hk hkm hret
  exact hline k hk hkm (normalizes_central_kernel_of_orbit_return P Z hZC
    (t ^ k) ((Subgroup.normalizer (Z : Set G)).pow_mem htZ k) x hret)

end SymmetricSubgroupAsymptotics.CentralKernelNormalizerOrbitPacking
