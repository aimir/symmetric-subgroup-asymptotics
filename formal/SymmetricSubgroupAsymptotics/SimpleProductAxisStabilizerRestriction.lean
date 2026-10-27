import SymmetricSubgroupAsymptotics.BurnsideTwoPrimeSolvability
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.GroupAction.Blocks
import Mathlib.Algebra.Group.Subgroup.Finite

/-! Literal axis intersections of coupled point stabilizers. No classification is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SimpleProductAxisStabilizerRestriction
variable {J T : Type} [Group T] [Finite T] [Fintype J] [DecidableEq J]

abbrev axis (i : J) : T →* (J → T) := MonoidHom.mulSingle (fun _ : J => T) i
abbrev coordinate (i : J) : (J → T) →* T := Pi.evalMonoidHom (fun _ : J => T) i

theorem intersection_normal (H : Subgroup (J → T)) (i : J)
    (hfull : H.map (coordinate i) = ⊤) : (H.comap (axis i)).Normal := by
  constructor
  intro a ha g
  have hg : g ∈ H.map (coordinate i) := by rw [hfull]; trivial
  obtain ⟨h, hh, hgi⟩ := hg
  have hc : axis i (g*a*g⁻¹) = h * axis i a * h⁻¹ := by
    funext j
    by_cases hj : j=i
    · subst j
      change h i=g at hgi
      simp only [axis,MonoidHom.mulSingle_apply,Pi.mulSingle_eq_same,
        Pi.mul_apply,Pi.inv_apply,hgi]
    · simp [axis,MonoidHom.mulSingle_apply,Pi.mulSingle,hj,Ne.symm hj]
  change axis i (g*a*g⁻¹) ∈ H
  rw [hc]
  exact H.mul_mem (H.mul_mem hh ha) (H.inv_mem hh)

private theorem axis_range_normal (i : J) : (axis (T:=T) i).range.Normal := by
  constructor
  rintro a ⟨t,rfl⟩ g
  refine ⟨g i*t*(g i)⁻¹,?_⟩
  funext j
  by_cases hj : j=i
  · subst j
    simp [axis,MonoidHom.mulSingle_apply]
  · simp [axis,MonoidHom.mulSingle_apply,Pi.mulSingle,hj,Ne.symm hj]

/-- A literal normal axis orbit divides the degree of the original transitive action. -/
theorem axis_index_dvd_index (H : Subgroup (J → T)) (i : J) :
    (H.comap (axis i)).index ∣ H.index := by
  let X := (J → T) ⧸ H
  let x : X := QuotientGroup.mk 1
  let K := (axis (T:=T) i).range
  letI : K.Normal := axis_range_normal i
  letI : MulAction T X := MulAction.compHom X (axis i)
  have hs : MulAction.stabilizer T x = H.comap (axis i) := by
    ext t
    rw [MulAction.mem_stabilizer_iff,Subgroup.mem_comap]
    rw [MulAction.compHom_smul_def]
    change axis i t • (QuotientGroup.mk (1 : J → T) : X)=QuotientGroup.mk 1 ↔ axis i t ∈ H
    rw [MulAction.Quotient.smul_mk]
    simp [smul_eq_mul,QuotientGroup.eq]
  have ho : MulAction.orbit T x = MulAction.orbit K x := by
    ext y
    constructor
    · rintro ⟨t,ht⟩
      exact ⟨⟨axis i t,⟨t,rfl⟩⟩,ht⟩
    · rintro ⟨a,ha⟩
      obtain ⟨t,ht⟩ := a.property
      refine ⟨t,?_⟩
      change axis i t • x=y
      rw [ht]
      exact ha
  have hd := (MulAction.IsBlock.orbit_of_normal (N:=K) x).ncard_dvd_card
    ⟨x,MulAction.mem_orbit_self x⟩
  rw [←hs,MulAction.index_stabilizer]
  change (MulAction.orbit T x).ncard ∣ Nat.card X
  rw [ho]
  exact hd

theorem projection_index_dvd_index (H : Subgroup (J → T)) (i : J) :
    (H.map (coordinate i)).index ∣ H.index :=
  H.index_map_dvd (fun t => ⟨fun _ => t,rfl⟩)

/-- Full projection at an active axis forces the whole simple order into the index. -/
theorem axis_le_or_card_dvd_index [IsSimpleGroup T]
    (H : Subgroup (J → T)) (i : J) (hfull : H.map (coordinate i)=⊤) :
    (axis i).range ≤ H ∨ Nat.card T ∣ H.index := by
  letI : (H.comap (axis i)).Normal := intersection_normal H i hfull
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H.comap (axis i)) inferInstance with hb|ht
  · right
    have hd := axis_index_dvd_index H i
    simpa only [hb,Subgroup.index_bot] using hd
  · left
    rintro a ⟨t,rfl⟩
    have hh : t ∈ H.comap (axis i) := by rw [ht]; trivial
    exact hh

/-- Burnside excludes every nonabelian simple order from the entire two-prime divisor menu. -/
theorem simple_order_not_dvd [IsSimpleGroup T] (hn : ¬IsMulCommutative T) (m : ℕ) :
    ¬Nat.card T ∣ 3*2^m := by
  intro hd
  obtain ⟨a,b,ha,hb,he⟩ := exists_dvd_and_dvd_of_dvd_mul hd
  obtain ⟨u,_,hu⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (show a ∣ 3^1 by simpa using ha)
  obtain ⟨v,_,hv⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hb
  have hc : Nat.card T=3^u*2^v := he.trans (by rw [hu,hv])
  letI : IsSolvable T := burnsideTwoPrimeSolvability.solvable T 3 2 u v
    Nat.prime_three Nat.prime_two hc
  exact hn (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance))

/-- Inactive axes may project fully; every active axis has proper projection. -/
theorem projection_ne_top_of_active [IsSimpleGroup T]
    (hn : ¬IsMulCommutative T) (H : Subgroup (J → T)) (i : J) (m : ℕ)
    (hdegree : H.index ∣ 3*2^m) (hactive : ¬(axis i).range ≤ H) :
    H.map (coordinate i) ≠ ⊤ := by
  intro hf
  rcases axis_le_or_card_dvd_index H i hf with hi|hd
  · exact hactive hi
  · exact simple_order_not_dvd hn m (hd.trans hdegree)

/-- A proper full subdirect subgroup cannot have index dividing three times a power of two. -/
theorem not_full_subdirect [IsSimpleGroup T] (hn : ¬IsMulCommutative T)
    (H : Subgroup (J → T)) (m : ℕ) (hdegree : H.index ∣ 3*2^m)
    (hproper : H ≠ ⊤) : ¬∀ i : J,H.map (coordinate i)=⊤ := by
  intro hf
  have hall : ∀ i : J,(axis i).range ≤ H := by
    intro i
    rcases axis_le_or_card_dvd_index H i (hf i) with hi|hd
    · exact hi
    · exact (simple_order_not_dvd hn m (hd.trans hdegree)).elim
  apply hproper
  apply top_unique
  intro f _
  exact Subgroup.pi_mem_of_mulSingle_mem f (fun i => hall i ⟨f i,rfl⟩)

end SymmetricSubgroupAsymptotics.SimpleProductAxisStabilizerRestriction
