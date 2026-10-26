import SymmetricSubgroupAsymptotics.SignedMonomialStabilizerClassBound
import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
import Mathlib.GroupTheory.GroupAction.Quotient

/-! The support of a fixed monomial vector is fixed by its actual
permutation image. A surjection onto the full permutation group therefore
retains the binomial support-orbit factor in the SAME vector stabilizer.
No independent replacement of the acting subgroup is made. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.SignedMonomialSupportOrbitIndex
open SignedMonomialFixedCoordinateCode SignedMonomialStabilizerClassBound

theorem support_choose_mul_stabilizer_le
    {G I K : Type*} [Group G] [Field K] [Finite G] [Finite I]
    (ρ : G →* ((I → K) ≃ₗ[K] (I → K)))
    (t : G →* Equiv.Perm I) (a : G → I → Kˣ)
    (hformula : ∀ (g : G) (w : I → K) (i : I),
      ρ g w i=(a g i : K)*w ((t g).symm i))
    (ht : Function.Surjective t) (v : I → K) :
    (Nat.card I).choose (Nat.card {i : I // v i≠0})*
      Nat.card (fixedSubgroup ρ v)≤Nat.card G := by
  letI : Fintype I := Fintype.ofFinite I
  let s : Finset I := Finset.univ.filter fun i => v i≠0
  let S : Set.powersetCard I s.card := Set.powersetCard.ofCard rfl
  let T := MulAction.stabilizer (Equiv.Perm I) (s : Set I)
  letI : MulAction.IsPretransitive (Equiv.Perm I) (Set.powersetCard I s.card) :=
    Set.powersetCard.isPretransitive
  have hs : s.card=Nat.card {i : I // v i≠0} := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  have hindex : T.index=(Nat.card I).choose s.card := by
    have he : T.index=(MulAction.stabilizer (Equiv.Perm I) S).index :=
      congrArg (fun H : Subgroup (Equiv.Perm I) => H.index)
        (Set.powersetCard.stabilizer_coe S).symm
    rw [he,MulAction.index_stabilizer_of_transitive,
      Set.powersetCard.card]
  have hle : fixedSubgroup ρ v≤T.comap t := by
    intro g hg
    change t g • (s : Set I)=(s : Set I)
    apply Set.ext
    intro i
    simp only [Set.mem_smul_set_iff_inv_smul_mem,Finset.mem_coe,
      s,Finset.mem_filter,Finset.mem_univ,true_and]
    change v ((t g).symm i)≠0 ↔ v i≠0
    have h := fixed_support_iff ρ t a hformula g v hg ((t g).symm i)
    simpa only [Equiv.apply_symm_apply] using h.symm
  have hidx : (Nat.card I).choose s.card≤(fixedSubgroup ρ v).index := by
    calc
      _=T.index := hindex.symm
      _=(T.comap t).index := (T.index_comap_of_surjective ht).symm
      _≤(fixedSubgroup ρ v).index := Subgroup.index_antitone hle
  rw [←hs]
  calc
    _≤(fixedSubgroup ρ v).index*Nat.card (fixedSubgroup ρ v) :=
      Nat.mul_le_mul_right _ hidx
    _=Nat.card G := by
      simpa only [Nat.mul_comm] using (fixedSubgroup ρ v).card_mul_index

end SymmetricSubgroupAsymptotics.SignedMonomialSupportOrbitIndex
