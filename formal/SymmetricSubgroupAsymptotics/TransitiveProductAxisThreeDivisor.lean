import SymmetricSubgroupAsymptotics.ProductAxisPrimePowerOrbit
import Mathlib.GroupTheory.GroupAction.Blocks
import Mathlib.Algebra.Group.Pointwise.Set.Card

/-! A nonbinary transitive product action of degree dividing3*2^m
has an actual coordinate-factor stabilizer index divisible by3. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.TransitiveProductAxisThreeDivisor
open ProductAxisPrimePowerOrbit
variable {J T X : Type} [Group T] [Finite T] [Fintype J] [DecidableEq J]
  [Finite X] [MulAction (J → T) X] [MulAction.IsPretransitive (J → T) X]

def axisRange (i : J) : Subgroup (J → T) := (MonoidHom.mulSingle (fun _ : J => T) i).range

instance axisRange_normal (i : J) : (axisRange (T:=T) i).Normal := by
  constructor
  rintro a ⟨t,rfl⟩ g
  refine ⟨g i*t*(g i)⁻¹,?_⟩
  funext j
  by_cases hj : j=i
  · subst j
    simp only [MonoidHom.mulSingle_apply,Pi.mulSingle_eq_same,Pi.mul_apply,Pi.inv_apply]
  · simp [MonoidHom.mulSingle_apply,Pi.mulSingle,hj,Ne.symm hj]

theorem axis_orbit_eq_range_orbit (i : J) (x : X) :
    letI : MulAction T X := axisAction i
    MulAction.orbit T x=MulAction.orbit (axisRange (T:=T) i) x := by
  letI : MulAction T X := axisAction i
  ext y
  constructor
  · rintro ⟨t,ht⟩
    exact ⟨⟨Pi.mulSingle i t,⟨t,rfl⟩⟩,ht⟩
  · rintro ⟨a,ha⟩
    obtain ⟨t,ht⟩ := a.property
    refine ⟨t,?_⟩
    change (Pi.mulSingle i t : J → T)=a.val at ht
    change (Pi.mulSingle i t : J → T) • x=y
    rw [ht]
    exact ha

theorem exists_axis_three_divisor (m : ℕ) (x₀ : X)
    (hdegree : Nat.card X ∣ 3*2^m)
    (hnot : ∀ r : ℕ,Nat.card X ≠ 2^r) :
    ∃ i : J,
      letI : MulAction T X := axisAction i
      3 ∣ (MulAction.stabilizer T x₀).index := by
  by_contra hnone
  have hnot3 (i : J) : ¬3 ∣ Nat.card (MulAction.orbit (axisRange (T:=T) i) x₀) := by
    have hh : ¬(letI : MulAction T X := axisAction i
        3 ∣ (MulAction.stabilizer T x₀).index) := fun hi => hnone ⟨i,hi⟩
    letI : MulAction T X := axisAction i
    rw [MulAction.index_stabilizer] at hh
    simpa only [axis_orbit_eq_range_orbit] using hh
  have haxis (i : J) (x : X) :
      letI : MulAction T X := axisAction i
      ∃ r : ℕ,Nat.card (MulAction.orbit T x)=2^r := by
    let K := axisRange (T:=T) i
    have hcard : Nat.card (MulAction.orbit K x)=Nat.card (MulAction.orbit K x₀) := by
      obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (J → T) x₀ x
      change (MulAction.orbit K x).ncard=(MulAction.orbit K x₀).ncard
      rw [←hg,←MulAction.smul_orbit_eq_orbit_smul K x₀ g,Set.ncard_smul_set]
    have hd : Nat.card (MulAction.orbit K x) ∣ 3*2^m :=
      ((MulAction.IsBlock.orbit_of_normal (N:=K) x).ncard_dvd_card
        ⟨x,MulAction.mem_orbit_self x⟩).trans hdegree
    have hcop : (Nat.card (MulAction.orbit K x)).Coprime 3 := by
      rw [hcard]
      exact (Nat.prime_three.coprime_iff_not_dvd.mpr (hnot3 i)).symm
    have hd2 : Nat.card (MulAction.orbit K x) ∣ 2^m := hcop.dvd_mul_left.mp hd
    obtain ⟨r,_,hr⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2
    letI : MulAction T X := axisAction i
    exact ⟨r,by simpa only [axis_orbit_eq_range_orbit] using hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r,hr⟩ := ProductAxisPrimePowerOrbit.card_orbit_prime_power 2 haxis x₀
  have he : MulAction.orbit (J → T) x₀=Set.univ :=
    MulAction.orbit_eq_univ (J → T) x₀
  rw [he] at hr
  change (Set.univ : Set X).ncard=2^r at hr
  rw [Set.ncard_univ] at hr
  exact hnot r hr

end SymmetricSubgroupAsymptotics.TransitiveProductAxisThreeDivisor
