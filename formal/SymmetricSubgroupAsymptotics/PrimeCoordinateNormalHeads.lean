import SymmetricSubgroupAsymptotics.PrimeCoordinateRanks
import SymmetricSubgroupAsymptotics.PrimeSubdirectNormalHead
import SymmetricSubgroupAsymptotics.RelativeAmbientTransport

/-!
# Relative heads in full coordinate subgroups

The absolute coordinate theorem bounds the character head of a full
subdirect subgroup.  The degree-eighteen application needs its relative
version: an arbitrary normal subgroup of the full subdirect core is bounded
by the relative normal heads of the original coordinate groups.

The proof keeps the actual correlated core.  At each coordinate it applies
`SubdirectNormalHead.relativeHead_le` to the image of the original normal
subgroup, then recurses on its exact image in the remaining coordinates.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]

/-- A normal subgroup of a complete full-coordinate subgroup is controlled
by the relative heads of literal normal subgroups in the same coordinate
groups.  No direct-product replacement or independence of coordinates is
used. -/
theorem primeRelativeHead_fullCoordinate_le (n : ℕ)
    (A : Fin n → Type*) [∀ i, Group (A i)] [∀ i, Finite (A i)]
    (c : Fin n → ℕ)
    (hbound : ∀ i (N : Subgroup (A i)) (hN : N.Normal),
      letI := hN
      Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤ c i)
    (K : Subgroup (∀ i, A i))
    (hfull : ∀ i, Function.Surjective (fun k : K => (k : ∀ i, A i) i))
    (M : Subgroup K) [M.Normal] :
    Module.finrank (ZMod p) (primeRelativeCharacters p M) ≤ ∑ i, c i := by
  induction n with
  | zero =>
    have hK : Subsingleton K := inferInstance
    have hM : Subsingleton M := inferInstance
    have hc : Subsingleton (primeRelativeCharacters p M) := by
      refine ⟨fun χ ψ => ?_⟩
      ext m
      have hm : m = 1 := Subsingleton.elim _ _
      simp only [hm]
      exact χ.1.map_zero.trans ψ.1.map_zero.symm
    letI := hc
    simpa only [Finset.sum_empty, Finset.univ_eq_empty, Nat.le_zero] using
      Module.finrank_zero_of_subsingleton
        (R := ZMod p) (M := primeRelativeCharacters p M)
  | succ n ih =>
    let tail : (∀ i : Fin (n + 1), A i) →* (∀ i : Fin n, A i.succ) :=
      { toFun := fun x i => x i.succ
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    let B : Subgroup (∀ i : Fin n, A i.succ) := K.map tail
    let φ : K →* (A 0 × B) :=
      { toFun := fun k =>
          ((k : ∀ i, A i) 0, ⟨tail k, ⟨k, k.2, rfl⟩⟩)
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hφ : Function.Injective φ := by
      intro x y he
      apply Subtype.ext
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact congrArg Prod.fst he
      · exact congrArg (fun z : A 0 × B =>
          (z.2 : ∀ i : Fin n, A i.succ) j) he
    let R : Subgroup (A 0 × B) := φ.range
    let e : K ≃* R := MonoidHom.ofInjective (f := φ) hφ
    let MR : Subgroup R := M.map e.toMonoidHom
    letI : MR.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
    have hA : Function.Surjective (Prod.fst ∘ R.subtype) := by
      intro a
      obtain ⟨k, hk⟩ := hfull 0 a
      exact ⟨⟨φ k, ⟨k, rfl⟩⟩, hk⟩
    have hB : Function.Surjective (Prod.snd ∘ R.subtype) := by
      rintro ⟨b, hb⟩
      obtain ⟨k, hk, hkb⟩ := hb
      refine ⟨⟨φ ⟨k, hk⟩, ⟨⟨k, hk⟩, rfl⟩⟩, ?_⟩
      exact Subtype.ext hkb
    have htail : ∀ i : Fin n,
        Function.Surjective (fun b : B => (b : ∀ i : Fin n, A i.succ) i) := by
      intro i a
      obtain ⟨k, hk⟩ := hfull i.succ a
      exact ⟨⟨tail k, ⟨k, k.2, rfl⟩⟩, hk⟩
    letI : (SubdirectNormalHead.firstAxis R MR).Normal :=
      SubdirectNormalHead.firstAxis_normal R MR hA
    letI : (SubdirectNormalHead.secondImage R MR).Normal :=
      SubdirectNormalHead.secondImage_normal R MR hB
    have hpair := SubdirectNormalHead.relativeHead_le R MR p hA hB
    have hrec := ih (fun i : Fin n => A i.succ) (fun i => c i.succ)
      (fun i => hbound i.succ) B htail
      (SubdirectNormalHead.secondImage R MR)
    have haxis := hbound 0 (SubdirectNormalHead.firstAxis R MR)
      (SubdirectNormalHead.firstAxis_normal R MR hA)
    have hR : Module.finrank (ZMod p) (primeRelativeCharacters p MR) ≤
        ∑ i : Fin (n + 1), c i := by
      rw [Fin.sum_univ_succ]
      exact (hpair.trans (Nat.add_le_add hrec haxis)).trans_eq
        (Nat.add_comm _ _)
    have heq : Module.finrank (ZMod p) (primeRelativeCharacters p MR) =
        Module.finrank (ZMod p) (primeRelativeCharacters p M) :=
      (relativeCharacterAmbientCongr p e M MR rfl).finrank_eq
    rwa [heq] at hR

/-- Faithful original coordinate maps give the same relative-head bound
without first replacing the physical core by a product subgroup. -/
theorem primeRelativeHead_faithful_family_le
    {G : Type*} [Group G] (n : ℕ)
    (A : Fin n → Type*) [∀ i, Group (A i)] [∀ i, Finite (A i)]
    (ρ : ∀ i, G →* A i)
    (honto : ∀ i, Function.Surjective (ρ i))
    (hfaithful : Function.Injective (fun g : G => fun i => ρ i g))
    (c : Fin n → ℕ)
    (hbound : ∀ i (N : Subgroup (A i)) (hN : N.Normal),
      letI := hN
      Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤ c i)
    (M : Subgroup G) [M.Normal] :
    Module.finrank (ZMod p) (primeRelativeCharacters p M) ≤ ∑ i, c i := by
  let f : G →* (∀ i, A i) :=
    { toFun := fun g i => ρ i g
      map_one' := by funext i; exact (ρ i).map_one
      map_mul' := by intro g h; funext i; exact (ρ i).map_mul g h }
  have hf : Function.Injective f := hfaithful
  let K : Subgroup (∀ i, A i) := f.range
  let e : G ≃* K := MonoidHom.ofInjective (f := f) hf
  let MK : Subgroup K := M.map e.toMonoidHom
  letI : MK.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  have hfull : ∀ i,
      Function.Surjective (fun k : K => (k : ∀ i, A i) i) := by
    intro i a
    obtain ⟨g, hg⟩ := honto i a
    exact ⟨⟨f g, ⟨g, rfl⟩⟩, hg⟩
  have hK := primeRelativeHead_fullCoordinate_le p n A c hbound K hfull MK
  have heq : Module.finrank (ZMod p) (primeRelativeCharacters p MK) =
      Module.finrank (ZMod p) (primeRelativeCharacters p M) :=
    (relativeCharacterAmbientCongr p e M MK rfl).finrank_eq
  rwa [heq] at hK

end SymmetricSubgroupAsymptotics

end
