import SymmetricSubgroupAsymptotics.PrimeCoordinateRanks
import SymmetricSubgroupAsymptotics.PrimeCharacterGenerators
import SymmetricSubgroupAsymptotics.PrimeCharacterSubgroupCapacity
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! Bounds on prime characters of every actual subgroup. The product step
uses the original projection kernel and image, with no fullness hypothesis.
For finite p-groups these are sectional generator-rank bounds; the character
statements themselves require neither commutativity nor p-group structure. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]

/-- Every subgroup is tested with its own complete character space. -/
def PrimeSectionalRankBound (G : Type*) [Group G] (r : ℕ) : Prop :=
  ∀ K : Subgroup G, Module.finrank (ZMod p) (PrimeCharacters p K) ≤ r

theorem primeCharacterRank_le_of_injective
    {G A : Type*} [Group G] [Group A] [Finite A] {r : ℕ}
    (hA : PrimeSectionalRankBound p A r) (f : G →* A)
    (hf : Function.Injective f) :
    Module.finrank (ZMod p) (PrimeCharacters p G) ≤ r := by
  rw [primeCharacter_finrank_congr p (MonoidHom.ofInjective (f := f) hf)]
  exact hA f.range

theorem PrimeSectionalRankBound.of_injective
    {G A : Type*} [Group G] [Group A] [Finite A] {r : ℕ}
    (hA : PrimeSectionalRankBound p A r) (f : G →* A)
    (hf : Function.Injective f) : PrimeSectionalRankBound p G r := by
  intro K
  exact primeCharacterRank_le_of_injective p hA (f.comp K.subtype)
    (hf.comp Subtype.val_injective)

/-- The quotient part of a section cannot increase prime character rank. -/
theorem PrimeSectionalRankBound.quotient_rank_le
    {G Q : Type*} [Group G] [Finite G] [Group Q] {r : ℕ}
    (hG : PrimeSectionalRankBound p G r) (K : Subgroup G)
    (f : K →* Q) (hf : Function.Surjective f) :
    Module.finrank (ZMod p) (PrimeCharacters p Q) ≤ r :=
  ((primeCharacterInflation p f).finrank_le_finrank_of_injective
    (primeCharacterInflation_injective p f hf)).trans (hG K)

/-- An actual joint embedding gives the extension estimate through the
second image and its literal kernel, without either projection being full. -/
theorem primeCharacterRank_le_of_pair_injective
    {G A B : Type*} [Group G] [Finite G] [Group A] [Finite A]
    [Group B] [Finite B] {r s : ℕ}
    (hA : PrimeSectionalRankBound p A r) (hB : PrimeSectionalRankBound p B s)
    (α : G →* A) (β : G →* B)
    (hfaithful : Function.Injective (fun g => (α g, β g))) :
    Module.finrank (ZMod p) (PrimeCharacters p G) ≤ r + s := by
  let π := β.rangeRestrict
  let κ : π.ker →* A := α.comp π.ker.subtype
  have hκ : Function.Injective κ := by
    intro x y hxy
    apply Subtype.ext
    apply hfaithful
    apply Prod.ext
    · exact hxy
    · have hx : β (x : G) = 1 :=
        congrArg (fun z : β.range => (z : B)) x.property
      have hy : β (y : G) = 1 :=
        congrArg (fun z : β.range => (z : B)) y.property
      exact hx.trans hy.symm
  have hk := primeCharacterRank_le_of_injective p hA κ hκ
  have hr := (Submodule.finrank_le (primeRelativeCharacters p π.ker)).trans hk
  have hext := primeCharacterRank_extension_le p π β.rangeRestrict_surjective
  exact (hext.trans (Nat.add_le_add (hB β.range) hr)).trans_eq (Nat.add_comm s r)

theorem PrimeSectionalRankBound.prod
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B] {r s : ℕ}
    (hA : PrimeSectionalRankBound p A r) (hB : PrimeSectionalRankBound p B s) :
    PrimeSectionalRankBound p (A × B) (r + s) := by
  intro K
  apply primeCharacterRank_le_of_pair_injective p hA hB
    ((MonoidHom.fst A B).comp K.subtype) ((MonoidHom.snd A B).comp K.subtype)
  intro x y hxy
  exact Subtype.ext hxy

/-- Restrict to the actual coordinate images, then apply the checked
full-coordinate theorem to that faithful range. No original fullness is needed. -/
theorem PrimeSectionalRankBound.pi (n : ℕ)
    (A : Fin n → Type*) [∀ i, Group (A i)] [∀ i, Finite (A i)]
    (c : Fin n → ℕ) (hA : ∀ i, PrimeSectionalRankBound p (A i) (c i)) :
    PrimeSectionalRankBound p (∀ i, A i) (∑ i, c i) := by
  intro K
  let ρ (i : Fin n) : K →* A i := (Pi.evalMonoidHom A i).comp K.subtype
  let J (i : Fin n) : Subgroup (A i) := (ρ i).range
  let f : K →* (∀ i, J i) := {
    toFun := fun x i => (ρ i).rangeRestrict x
    map_one' := by funext i; exact (ρ i).rangeRestrict.map_one
    map_mul' := by intro x y; funext i; exact (ρ i).rangeRestrict.map_mul x y }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext i
    exact congrArg (fun z : ∀ i, J i => (z i : A i)) hxy
  have hfull : ∀ i, Function.Surjective (fun x : f.range => (x : ∀ i, J i) i) := by
    intro i y
    obtain ⟨x, hx⟩ := (ρ i).rangeRestrict_surjective y
    exact ⟨⟨f x, ⟨x, rfl⟩⟩, hx⟩
  have hnormal : ∀ i (N : Subgroup (J i)) (hN : N.Normal),
      letI := hN
      Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤ c i := by
    intro i N hN
    letI := hN
    exact (Submodule.finrank_le _).trans
      (PrimeSectionalRankBound.of_injective p (hA i)
        (J i).subtype Subtype.val_injective N)
  rw [primeCharacter_finrank_congr p (MonoidHom.ofInjective (f := f) hf)]
  exact primeCharacterRank_coordinate_le p n (fun i => ↥(J i)) c hnormal f.range hfull

/-- Cyclic subgroups have one actual generator, even when their order is
not prime. In particular a C4 coordinate costs one, rather than two. -/
theorem primeSectionalRankBound_cyclic
    (G : Type*) [Group G] [IsCyclic G] : PrimeSectionalRankBound p G 1 := by
  intro K
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp
    (inferInstance : IsCyclic K)
  have hgen : Subgroup.closure (({g} : Finset K) : Set K) = ⊤ := by
    simpa only [Finset.coe_singleton, ← Subgroup.zpowers_eq_closure] using hg
  simpa only [Finset.card_singleton] using primeCharacterRank_le_generators p {g} hgen

/-- Order bounds control every actual subgroup, independently of normality. -/
theorem primeSectionalRankBound_of_card_le
    (G : Type*) [Group G] [Finite G] (u : ℕ) (hG : Nat.card G ≤ p ^ u) :
    PrimeSectionalRankBound p G u := by
  intro K
  apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
  exact (primeCharacters_pow_finrank_le_card p K).trans
    ((Nat.card_le_card_of_injective K.subtype Subtype.val_injective).trans hG)

/-- The scalar cyclic-four product has sectional binary rank at most its
number of original coordinates. -/
theorem binarySectionalRankBound_cyclicFour (a : ℕ) :
    PrimeSectionalRankBound 2 (Multiplicative (Fin a → ZMod 4)) a := by
  let f : Multiplicative (Fin a → ZMod 4) →* (Fin a → Multiplicative (ZMod 4)) := {
    toFun := fun x i => Multiplicative.ofAdd (x.toAdd i)
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Multiplicative.toAdd.injective
    funext i
    exact congrArg (fun z : Fin a → Multiplicative (ZMod 4) => (z i).toAdd) hxy
  have h := PrimeSectionalRankBound.pi 2 a (fun _ => Multiplicative (ZMod 4))
    (fun _ => 1) (fun _ => primeSectionalRankBound_cyclic 2 _)
  have h' : PrimeSectionalRankBound 2 (Fin a → Multiplicative (ZMod 4)) a := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul, mul_one] using h
  exact PrimeSectionalRankBound.of_injective 2 h' f hf

/-- Uniform over all actual subgroups of C4^a × B, with arbitrary finite B. -/
theorem binarySectionalRankBound_cyclicFour_prod
    (a : ℕ) (B : Type*) [Group B] [Finite B] (u : ℕ)
    (hB : Nat.card B ≤ 2 ^ u) :
    PrimeSectionalRankBound 2 (Multiplicative (Fin a → ZMod 4) × B) (a + u) :=
  PrimeSectionalRankBound.prod 2 (binarySectionalRankBound_cyclicFour a)
    (primeSectionalRankBound_of_card_le 2 B u hB)

end SymmetricSubgroupAsymptotics
