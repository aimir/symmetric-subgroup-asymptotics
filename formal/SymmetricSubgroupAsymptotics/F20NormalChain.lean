import SymmetricSubgroupAsymptotics.AffineIrreducibleNormalGenerators
import SymmetricSubgroupAsymptotics.Non2PreE7F20MarkedC4Source

/-!
# Normal chains for cyclic prime-power groups and the faithful F20 model

Subgroups of a finite cyclic group are the kernels of the corresponding
power maps. Divisibility of subgroup orders therefore gives inclusion.
Prime-power orders make all such subgroups comparable. Applying the
irreducible-affine normal-chain theorem to the existing faithful F20 model
gives its normal chain without enumerating any normal subgroup.

An explicit scalar-coordinate semidirect product is also identified with
that existing model. Its forward action is executable on field elements,
so selected literal representations can be bound using small scalar checks.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

theorem cyclic_subgroup_le_of_card_dvd
    {A : Type*} [CommGroup A] [Finite A] [IsCyclic A]
    (M N : Subgroup A) (hcard : Nat.card M ∣ Nat.card N) : M ≤ N := by
  intro x hx
  have hp : x ^ Nat.card M = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (G := M) (x := ⟨x, hx⟩))
  rw [← cyclic_ker_powCard N, MonoidHom.mem_ker, powMonoidHom_apply]
  obtain ⟨k, hk⟩ := hcard
  rw [hk, pow_mul, hp, one_pow]

/-- Every pair of actual subgroups of a cyclic prime-power group is comparable. -/
theorem cyclic_primePower_subgroups_total
    {A : Type*} [CommGroup A] [Finite A] [IsCyclic A]
    {p n : ℕ} (hp : p.Prime) (hcard : Nat.card A = p ^ n)
    (M N : Subgroup A) : M ≤ N ∨ N ≤ M := by
  have hM : Nat.card M ∣ p ^ n := hcard ▸ M.card_subgroup_dvd_card
  have hN : Nat.card N ∣ p ^ n := hcard ▸ N.card_subgroup_dvd_card
  obtain ⟨r, _hrn, hr⟩ := (Nat.dvd_prime_pow hp).mp hM
  obtain ⟨s, _hsn, hs⟩ := (Nat.dvd_prime_pow hp).mp hN
  rcases le_total r s with h | h
  · left
    apply cyclic_subgroup_le_of_card_dvd M N
    rw [hr, hs]
    exact Nat.pow_dvd_pow p h
  · right
    apply cyclic_subgroup_le_of_card_dvd N M
    rw [hr, hs]
    exact Nat.pow_dvd_pow p h

namespace F20

open AffineModel

def complementC4Equiv : R ≃* Multiplicative (ZMod 4) :=
  (Subgroup.topEquiv : R ≃* GLV 5 1).trans c4Equiv

theorem complement_normal_total (A B : Subgroup R)
    (hA : A.Normal) (hB : B.Normal) : A ≤ B ∨ B ≤ A := by
  apply normalSubgroups_total_of_surjective
    complementC4Equiv.symm.toMonoidHom complementC4Equiv.symm.surjective _ A B hA hB
  intro M N _hM _hN
  apply cyclic_primePower_subgroups_total (p := 2) (n := 2) Nat.prime_two _ M N
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  norm_num

/-- The existing faithful one-dimensional affine model has a normal chain. -/
theorem normal_total (A B : Subgroup G)
    (hA : A.Normal) (hB : B.Normal) : A ≤ B ∨ B ≤ A :=
  normal_total_of_irreducible_complement R irreducible complement_normal_total A B hA hB

/-- Use field units as concrete coordinates for the actual linear complement. -/
def scalarInclusion : (ZMod 5)ˣ ≃* R :=
  scalarEquiv.trans (Subgroup.topEquiv : R ≃* GLV 5 1).symm

def scalarAction : (ZMod 5)ˣ →* MulAut (Multiplicative (V 5 1)) :=
  (AffineModel.linAut R).comp scalarInclusion.toMonoidHom

abbrev ScalarModel := Multiplicative (V 5 1) ⋊[scalarAction] (ZMod 5)ˣ

/-- This scalar-coordinate model is equivalent to the original F20 model. -/
def scalarModelEquiv : ScalarModel ≃* G :=
  SemidirectProduct.congr (MulEquiv.refl _) scalarInclusion (by
    intro u
    apply MulEquiv.ext
    intro v
    rfl)

theorem scalarModel_normal_total (A B : Subgroup ScalarModel)
    (hA : A.Normal) (hB : B.Normal) : A ≤ B ∨ B ≤ A :=
  normalSubgroups_total_of_surjective scalarModelEquiv.symm.toMonoidHom
    scalarModelEquiv.symm.surjective normal_total A B hA hB

end F20
end SymmetricSubgroupAsymptotics

end
