import SymmetricSubgroupAsymptotics.Non2SchurRowProfile
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# The first nonfixed Schur degree

Over the binary field, a one-dimensional representation is trivial.  Hence
an actual nonfixed simple row cannot have Schur product degree one.  This
removes the only numerical case below the scalar `C₃` row.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {B A : Type} [Group B]
    [AddCommGroup A] [Module (ZMod 2) A]

/-- Every linear automorphism of a one-dimensional binary vector space is
the identity, applied to the action on an actual module subspace. -/
theorem representationSubmoduleFixed_of_binary_finrank_one
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    (hS : Module.finrank (ZMod 2) S = 1) :
    representationSubmoduleFixed (k := ZMod 2) (B := B) (A := A) sigma S := by
  intro g x
  let rhoS : Representation (ZMod 2) B S :=
    Representation.ofModule' S
  obtain ⟨c, hc, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hS
      (rhoS g)
  letI : Nontrivial S := Module.nontrivial_of_finrank_pos (by
    rw [hS]
    decide)
  have hcne : c ≠ 0 := by
    intro hc0
    have hz : rhoS g = 0 := by
      rw [hc, hc0, zero_smul]
    obtain ⟨y, hy⟩ := exists_ne (0 : S)
    have hzero : y = 0 := by
      calc
        y = rhoS g (rhoS g⁻¹ y) := by simp [rhoS]
        _ = 0 := by rw [hz]; rfl
    exact hy hzero
  have hc1 : c = 1 := by
    have hbits : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
    exact (hbits c).resolve_left hcne
  have hact : rhoS g x = x := by
    have hx := LinearMap.congr_fun hc x
    rw [hc1] at hx
    simpa using hx
  change rhoS g x = x
  exact hact

/-- A nonfixed actual simple row has Schur product degree at least two. -/
theorem two_le_schurSimpleProductDegree_of_nonfixed
    [FiniteDimensional (ZMod 2) A]
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    [IsSimpleModule (ZMod 2)[B] S]
    (hnonfixed : ¬ representationSubmoduleFixed
      (k := ZMod 2) (B := B) (A := A) sigma S) :
    2 ≤ schurSimpleProductDegree sigma S := by
  haveI : FiniteDimensional (ZMod 2) S :=
    FiniteDimensional.of_injective
      (S.subtype.restrictScalars (ZMod 2)) S.subtype_injective
  haveI : Nontrivial S := IsSimpleModule.nontrivial (ZMod 2)[B] S
  have hdNat : 0 < Module.finrank (Module.End (ZMod 2)[B] S) S := by
    have htower := schur_simple_finrank_tower
      (k := ZMod 2) (R := (ZMod 2)[B]) (X := S)
    have hh : 0 < Module.finrank (ZMod 2) S :=
      Module.finrank_pos (R := ZMod 2) (M := S)
    by_contra hd
    have hd0 : Module.finrank (Module.End (ZMod 2)[B] S) S = 0 :=
      Nat.eq_zero_of_not_pos hd
    rw [hd0, Nat.mul_zero] at htower
    omega
  have hpos : 0 < schurSimpleProductDegree sigma S := by
    unfold schurSimpleProductDegree
    exact Nat.mul_pos
      (Module.finrank_pos (R := ZMod 2) (M := S))
      hdNat
  by_contra hnot
  have hone : schurSimpleProductDegree sigma S = 1 := by omega
  have hdim : Module.finrank (ZMod 2) S = 1 := by
    unfold schurSimpleProductDegree at hone
    exact Nat.dvd_one.mp ⟨_, hone.symm⟩
  exact hnonfixed
    (representationSubmoduleFixed_of_binary_finrank_one sigma S hdim)

/-- Equality in the first possible nonfixed Schur degree forces the
two-dimensional, Schur-dimension-one profile used by the scalar `C₃`
branch. -/
theorem schurSimpleProductDegree_eq_two_profile
    [FiniteDimensional (ZMod 2) A]
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    [IsSimpleModule (ZMod 2)[B] S]
    (hnonfixed : ¬ representationSubmoduleFixed
      (k := ZMod 2) (B := B) (A := A) sigma S)
    (hq : schurSimpleProductDegree sigma S = 2) :
    Module.finrank (ZMod 2) S = 2 ∧
      Module.finrank (Module.End (ZMod 2)[B] S) S = 1 := by
  let h := Module.finrank (ZMod 2) S
  let d := Module.finrank (Module.End (ZMod 2)[B] S) S
  have hmul : h * d = 2 := by
    simpa [h, d, schurSimpleProductDegree] using hq
  have hdvd : h ∣ 2 := ⟨d, hmul.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hh | hh
  · have hfixed := representationSubmoduleFixed_of_binary_finrank_one
      sigma S (by simpa [h] using hh)
    exact (hnonfixed hfixed).elim
  · have hd : d = 1 := by
      rw [hh] at hmul
      omega
    exact ⟨by simpa [h] using hh, by simpa [d] using hd⟩

/-- In the degree-two row the actual Schur division ring has binary
dimension two, hence four elements. -/
theorem schurSimpleProductDegree_eq_two_end_finrank
    [FiniteDimensional (ZMod 2) A]
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    [IsSimpleModule (ZMod 2)[B] S]
    (hnonfixed : ¬ representationSubmoduleFixed
      (k := ZMod 2) (B := B) (A := A) sigma S)
    (hq : schurSimpleProductDegree sigma S = 2) :
    Module.finrank (ZMod 2) (Module.End (ZMod 2)[B] S) = 2 := by
  haveI : FiniteDimensional (ZMod 2) S :=
    FiniteDimensional.of_injective
      (S.subtype.restrictScalars (ZMod 2)) S.subtype_injective
  haveI : Nontrivial S := IsSimpleModule.nontrivial (ZMod 2)[B] S
  obtain ⟨hh, hd⟩ := schurSimpleProductDegree_eq_two_profile
    sigma S hnonfixed hq
  have htower := schur_simple_finrank_tower
    (k := ZMod 2) (R := (ZMod 2)[B]) (X := S)
  rw [hh, hd, Nat.mul_one] at htower
  exact htower.symm

end SymmetricSubgroupAsymptotics

end
