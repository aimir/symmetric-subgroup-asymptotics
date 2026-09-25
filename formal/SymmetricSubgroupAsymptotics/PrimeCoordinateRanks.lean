import SymmetricSubgroupAsymptotics.PrimeSubdirectRank

/-! Relative-head bounds on original coordinate actions control every
full subdirect subgroup. This is the orbit-filtration mechanism, before
any classification or numerical bound is substituted for its local heads. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics
variable (p : ℕ) [Fact p.Prime]

/-- Every complete full-coordinate subgroup is bounded using relative
heads of literal normal subgroups of those same coordinate actions.
This does not add the ranks of the whole coordinate images. -/
theorem primeCharacterRank_coordinate_le (n : ℕ)
    (A : Fin n → Type*) [∀ i,Group (A i)] [∀ i,Finite (A i)]
    (c : Fin n → ℕ)
    (hbound : ∀ i (N : Subgroup (A i)) (hN : N.Normal),
      letI := hN
      Module.finrank (ZMod p) (primeRelativeCharacters p N)≤c i)
    (K : Subgroup (∀ i,A i))
    (hfull : ∀ i,Function.Surjective (fun k : K => (k:∀ i,A i) i)) :
    Module.finrank (ZMod p) (PrimeCharacters p K) ≤ ∑ i,c i := by
  induction n with
  | zero =>
    have hK : Subsingleton K := inferInstance
    have hc : Subsingleton (PrimeCharacters p K) := by
      refine ⟨fun χ ψ => ?_⟩
      ext k
      have hk : (k:K)=1 := Subsingleton.elim _ _
      simp only [hk]
      exact χ.map_zero.trans ψ.map_zero.symm
    letI := hc
    simpa only [Finset.sum_empty,Finset.univ_eq_empty,Nat.le_zero] using
      Module.finrank_zero_of_subsingleton (R := ZMod p) (M := PrimeCharacters p K)
  | succ n ih =>
    let tail : (∀ i:Fin (n+1),A i) →* (∀ i:Fin n,A i.succ) := {
      toFun := fun x i => x i.succ
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    let B : Subgroup (∀ i:Fin n,A i.succ) := K.map tail
    let φ : K →* (A 0 × B) := {
      toFun := fun k => ((k:∀ i,A i) 0,⟨tail k,⟨k,k.2,rfl⟩⟩)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    have hφ : Function.Injective φ := by
      intro x y he
      apply Subtype.ext
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact congrArg Prod.fst he
      · exact congrArg (fun z : A 0 × B => (z.2:∀ i:Fin n,A i.succ) j) he
    let R := φ.range
    have hA : Function.Surjective (Prod.fst ∘ R.subtype) := by
      intro a
      obtain ⟨k,hk⟩ := hfull 0 a
      exact ⟨⟨φ k,⟨k,rfl⟩⟩,hk⟩
    have hB : Function.Surjective (Prod.snd ∘ R.subtype) := by
      rintro ⟨b,hb⟩
      obtain ⟨k,hk,hkb⟩ := hb
      refine ⟨⟨φ ⟨k,hk⟩,⟨⟨k,hk⟩,rfl⟩⟩,?_⟩
      exact Subtype.ext hkb
    have htail : ∀ i:Fin n,Function.Surjective (fun b : B => (b:∀ i:Fin n,A i.succ) i) := by
      intro i a
      obtain ⟨k,hk⟩ := hfull i.succ a
      exact ⟨⟨tail k,⟨k,k.2,rfl⟩⟩,hk⟩
    have hrec := ih (fun i:Fin n => A i.succ) (fun i => c i.succ)
      (fun i => hbound i.succ) B htail
    have hpair := primeCharacterRank_subdirect_le p R hA hB
    letI := Subgroup.normal_goursatFst hA
    have haxis := hbound 0 R.goursatFst (Subgroup.normal_goursatFst hA)
    have he := primeCharacter_finrank_congr p (MonoidHom.ofInjective (f := φ) hφ)
    rw [he]
    rw [Fin.sum_univ_succ]
    exact (hpair.trans (Nat.add_le_add hrec haxis)).trans_eq (Nat.add_comm _ _)

/-- A high complete source has an actual high relative normal pair in
one of its original coordinate actions. Classification is applied only
after this witness has been produced. -/
theorem primeCharacterRank_coordinate_high (n : ℕ)
    (A : Fin n → Type*) [∀ i,Group (A i)] [∀ i,Finite (A i)]
    (w : Fin n → ℕ) (q : ℕ) (hq : 0<q)
    (K : Subgroup (∀ i,A i))
    (hfull : ∀ i,Function.Surjective (fun k : K => (k:∀ i,A i) i))
    (hhigh : ∑ i,w i < q*Module.finrank (ZMod p) (PrimeCharacters p K)) :
    ∃ i, ∃ (N : Subgroup (A i)) (hN : N.Normal),
      letI := hN
      w i < q*Module.finrank (ZMod p) (primeRelativeCharacters p N) := by
  by_contra h
  push Not at h
  have hb : ∀ i (N : Subgroup (A i)) (hN : N.Normal),
      letI := hN
      Module.finrank (ZMod p) (primeRelativeCharacters p N)≤w i/q := by
    intro i N hN
    exact (Nat.le_div_iff_mul_le hq).mpr (by simpa only [Nat.mul_comm] using h i N hN)
  have hr := primeCharacterRank_coordinate_le p n A (fun i => w i/q) hb K hfull
  have hs : q*(∑ i,w i/q)≤∑ i,w i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => Nat.mul_div_le (w i) q)
  have hh := (Nat.mul_le_mul_left q hr).trans hs
  omega

/-- The high-pair witness applies directly to a faithful family of
original action maps, without replacing the source by a direct product. -/
theorem primeCharacterRank_faithful_family_high
    {G : Type*} [Group G] (n : ℕ)
    (A : Fin n → Type*) [∀ i,Group (A i)] [∀ i,Finite (A i)]
    (ρ : ∀ i,G →* A i)
    (honto : ∀ i,Function.Surjective (ρ i))
    (hfaithful : Function.Injective (fun g : G => fun i => ρ i g))
    (w : Fin n → ℕ) (q : ℕ) (hq : 0<q)
    (hhigh : ∑ i,w i < q*Module.finrank (ZMod p) (PrimeCharacters p G)) :
    ∃ i, ∃ (N : Subgroup (A i)) (hN : N.Normal),
      letI := hN
      w i < q*Module.finrank (ZMod p) (primeRelativeCharacters p N) := by
  let f : G →* (∀ i,A i) := {
    toFun := fun g i => ρ i g
    map_one' := by funext i; exact (ρ i).map_one
    map_mul' := by intro g h; funext i; exact (ρ i).map_mul g h }
  have hf : Function.Injective f := hfaithful
  have he := primeCharacter_finrank_congr p (MonoidHom.ofInjective (f := f) hf)
  have hs : ∀ i,Function.Surjective (fun k : f.range => (k:∀ i,A i) i) := by
    intro i a
    obtain ⟨g,hg⟩ := honto i a
    exact ⟨⟨f g,⟨g,rfl⟩⟩,hg⟩
  exact primeCharacterRank_coordinate_high p n A w q hq f.range hs (he ▸ hhigh)

end SymmetricSubgroupAsymptotics
