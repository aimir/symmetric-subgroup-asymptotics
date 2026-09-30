import SymmetricSubgroupAsymptotics.CoprimeSplitCharacterLabel

/-!
# Orbit-injective characters on sign and Frobenius quotient targets

Two specializations of the coprime split label are used by the degree-six
owners.

* Ternary sign targets: `A` is an elementary abelian `3`-section of index two,
  and conjugation by one element `s` outside `A` is nontrivial on `A`.
* Binary Frobenius targets: `A` is an elementary abelian `2`-section of index
  three, and conjugation by one element `c` outside `A` is nontrivial.

In either case one character of `A` whose values on a conjugation orbit
detect every nonidentity element suffices.  The averaged character and the
detection property required by the general label are derived here from the
literal conjugation action.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical commutatorElement

namespace SymmetricSubgroupAsymptotics

private theorem zmod3_three_nsmul : ∀ y : ZMod 3, 3 • y = 0 := by decide

private theorem zmod3_average : ∀ a b : ZMod 3,
    a + b = ((2 : ℕ) : ZMod 3) * (2 • (a + b)) := by decide

private theorem zmod2_two_nsmul : ∀ y : ZMod 2, 2 • y = 0 := by decide

private theorem zmod2_average : ∀ a b d : ZMod 2,
    a + (b + d) = ((3 : ℕ) : ZMod 2) * (a + b + d) := by decide

variable {Q : Type*} [Group Q]

theorem mem_or_inv_mul_mem_of_index_two (A : Subgroup Q) [A.Normal] [Fintype (Q ⧸ A)]
    {s : Q} (hs : s ∉ A) (hindex : Nat.card (Q ⧸ A) = 2) (x : Q) :
    x ∈ A ∨ s⁻¹ * x ∈ A := by
  by_contra h
  push_neg at h
  have h1 : (QuotientGroup.mk x : Q ⧸ A) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact h.1
  have hs1 : (QuotientGroup.mk s : Q ⧸ A) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact hs
  have hxs : (QuotientGroup.mk x : Q ⧸ A) ≠ QuotientGroup.mk s := by
    intro he
    exact h.2 (QuotientGroup.eq.mp he.symm)
  have hcard : ({1, QuotientGroup.mk s, QuotientGroup.mk x} : Finset (Q ⧸ A)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hxs)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hs1.symm, h1.symm⟩
  have hle := Finset.card_le_univ ({1, QuotientGroup.mk s, QuotientGroup.mk x} :
    Finset (Q ⧸ A))
  rw [hcard, ← Nat.card_eq_fintype_card, hindex] at hle
  omega

theorem conjNormal_self_of_mem (A : Subgroup Q) [A.Normal]
    (hA : ∀ a b : A, a * b = b * a) {u : Q} (hu : u ∈ A) (v : A) :
    MulAut.conjNormal u v = v := by
  have h := conjNormal_eq_of_mem A hA (u := 1) (u' := u) (by simpa using hu) v
  rw [h]
  apply Subtype.ext
  simp

/-- Ternary sign targets. -/
theorem groupEpimorphism_card_le_ternarySign
    {J : Type*} [Group J] [Finite J] [Finite Q]
    (A : Subgroup Q) [A.Normal] [Fintype (Q ⧸ A)] (hA : ∀ a b : A, a * b = b * a)
    (h3 : ∀ a : A, a ^ 3 = 1) (hsq : ∀ x : Q, x ^ 2 ∈ A)
    (s : Q) (hs : s ∉ A) (hindex : Nat.card (Q ⧸ A) = 2)
    (ι : A →* Multiplicative (ZMod 3))
    (hι : ∀ v : A, ι v = 1 → ι (MulAut.conjNormal s v) = 1 → v = 1)
    (hσ : ∃ v : A, MulAut.conjNormal s v ≠ v) :
    Nat.card (GroupEpimorphism J Q) ≤
      Nat.card (PrimeCharacters 3 (commPowSubgroup J 2)) * Nat.card (Q ≃* Q) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let σ : A →* A := (MulAut.conjNormal s).toMonoidHom
  have hσapply (v : A) : σ v = MulAut.conjNormal s v := rfl
  have hσσ (v : A) : σ (σ v) = v := by
    have h := conjNormal_self_of_mem A hA (hsq s) v
    rw [pow_two, map_mul] at h
    exact h
  have hQA := mem_or_inv_mul_mem_of_index_two A hs hindex
  have hcomm : ∀ x y : Q, ⁅x, y⁆ ∈ A := by
    intro x y
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' A ⁅x, y⁆ = 1
    rw [map_commutatorElement]
    have hsq' (z : Q ⧸ A) : z * z = 1 := by
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
      rw [← QuotientGroup.mk_mul, ← pow_two, QuotientGroup.eq_one_iff]
      exact hsq z
    have hcomm' (a b : Q ⧸ A) : a * b = b * a := by
      have hab := hsq' (a * b)
      calc a * b = (a * b) * (b * a) * (b * a)⁻¹ := by group
        _ = (a * (b * b) * a) * (b * a)⁻¹ := by group
        _ = b * a := by
          rw [hsq' b, mul_one, hsq' a, one_mul]
          exact inv_eq_of_mul_eq_one_right (hsq' (b * a))
    rw [commutatorElement_def, hcomm' (QuotientGroup.mk' A x) (QuotientGroup.mk' A y)]
    group
  have hx3 (x : Multiplicative (ZMod 3)) : x ^ 3 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    exact zmod3_three_nsmul x.toAdd
  have hx2 (x : Multiplicative (ZMod 3)) (h : x ^ 2 = 1) : x = 1 := by
    calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
      _ = 1 := by rw [hx3, h, inv_one, mul_one]
  let ℓ0 : A →* Multiplicative (ZMod 3) :=
    { toFun := fun v => (ι v * ι (σ v)) ^ 2
      map_one' := by simp
      map_mul' := fun v w => by
        simp only [map_mul]
        rw [mul_mul_mul_comm, mul_pow] }
  apply groupEpimorphism_card_le_coprimeSplitLabel 3 2 (by norm_num) A hA hcomm hsq ι ℓ0
  · intro v
    have hne : (1 : Q ⧸ A) ≠ QuotientGroup.mk s := by
      intro h
      exact hs ((QuotientGroup.eq_one_iff s).mp h.symm)
    have huniv : (Finset.univ : Finset (Q ⧸ A)) = {1, QuotientGroup.mk s} := by
      symm
      apply Finset.eq_univ_of_card
      rw [Finset.card_pair hne, ← Nat.card_eq_fintype_card, hindex]
    rw [huniv, Finset.sum_pair hne]
    have h1 : MulAut.conjNormal (Quotient.out (1 : Q ⧸ A) : Q) v = v := by
      apply conjNormal_self_of_mem A hA
      rw [← QuotientGroup.eq_one_iff]
      exact Quotient.out_eq _
    have hs' : MulAut.conjNormal (Quotient.out (QuotientGroup.mk s : Q ⧸ A) : Q) v = σ v := by
      apply conjNormal_eq_of_mem A hA
      rw [← QuotientGroup.eq]
      exact (Quotient.out_eq _).symm
    rw [h1, hs', hindex]
    change (ι v).toAdd + (ι (σ v)).toAdd = (2 : ℕ) * ((ι v * ι (σ v)) ^ 2).toAdd
    rw [toAdd_pow, toAdd_mul]
    exact zmod3_average _ _
  · intro w hw1 hw0
    by_cases hwA : w ∈ A
    · let w' : A := ⟨w, hwA⟩
      have hcw : (⟨⁅w, s⁆, hcomm w s⟩ : A) = w' * (σ w')⁻¹ := by
        apply Subtype.ext
        simp [commutatorElement_def, hσapply, MulAut.conjNormal_apply, w', mul_assoc]
      have hu := hw1 s
      rw [hcw] at hu
      have hσu : σ (w' * (σ w')⁻¹) = (w' * (σ w')⁻¹)⁻¹ := by
        rw [map_mul, map_inv, hσσ, mul_inv_rev, inv_inv]
      have hu1 : w' * (σ w')⁻¹ = 1 :=
        hι _ hu (by rw [← hσapply, hσu, map_inv, hu, inv_one])
      have hfix : σ w' = w' := (mul_inv_eq_one.mp hu1).symm
      have hw0' : ℓ0 (w' ^ 2) = 1 := by
        have hwq : (⟨w ^ 2, hsq w⟩ : A) = w' ^ 2 := Subtype.ext rfl
        rw [← hwq]
        exact hw0
      change (ι (w' ^ 2) * ι (σ (w' ^ 2))) ^ 2 = 1 at hw0'
      rw [map_pow σ, hfix, map_pow ι, ← pow_add, ← pow_mul] at hw0'
      have hι1 : ι w' = 1 := by
        apply hx2
        calc ι w' ^ 2 = (ι w' ^ 3) ^ 2 * ι w' ^ 2 := by rw [hx3, one_pow, one_mul]
          _ = ι w' ^ ((2 + 2) * 2) := by group
          _ = 1 := hw0'
      have hw'1 : w' = 1 := hι w' hι1 (by rw [← hσapply, hfix, hι1])
      exact congrArg Subtype.val hw'1
    · exfalso
      obtain ⟨v, hv⟩ := hσ
      have hsw : s⁻¹ * w ∈ A := (hQA w).resolve_left hwA
      have hconj (a : A) : MulAut.conjNormal w a = σ a :=
        conjNormal_eq_of_mem A hA hsw a
      have hu (a : A) : σ a * a⁻¹ = 1 := by
        have ha := hw1 a
        have hca : (⟨⁅w, (a : Q)⁆, hcomm w a⟩ : A) = σ a * a⁻¹ := by
          rw [← hconj]
          apply Subtype.ext
          simp [commutatorElement_def, MulAut.conjNormal_apply]
        rw [hca] at ha
        have hσu : σ (σ a * a⁻¹) = (σ a * a⁻¹)⁻¹ := by
          rw [map_mul, map_inv, hσσ, mul_inv_rev, inv_inv]
        exact hι _ ha (by rw [← hσapply, hσu, map_inv, ha, inv_one])
      exact hv (mul_inv_eq_one.mp (hu v))

/-- Binary Frobenius targets. -/
theorem groupEpimorphism_card_le_binaryFrobenius
    {J : Type*} [Group J] [Finite J] [Finite Q]
    (A : Subgroup Q) [A.Normal] [Fintype (Q ⧸ A)] (hA : ∀ a b : A, a * b = b * a)
    (h2 : ∀ a : A, a ^ 2 = 1) (hcube : ∀ x : Q, x ^ 3 ∈ A)
    (c : Q) (hc : c ∉ A) (hindex : Nat.card (Q ⧸ A) = 3)
    (ι : A →* Multiplicative (ZMod 2))
    (hι : ∀ v : A, ι v = 1 → ι (MulAut.conjNormal c v) = 1 →
      ι (MulAut.conjNormal c (MulAut.conjNormal c v)) = 1 → v = 1)
    (hσ : ∃ v : A, MulAut.conjNormal c v ≠ v) :
    Nat.card (GroupEpimorphism J Q) ≤
      Nat.card (PrimeCharacters 2 (commPowSubgroup J 3)) * Nat.card (Q ≃* Q) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let σ : A →* A := (MulAut.conjNormal c).toMonoidHom
  have hσapply (v : A) : σ v = MulAut.conjNormal c v := rfl
  have hσ3 (v : A) : σ (σ (σ v)) = v := by
    have h := conjNormal_self_of_mem A hA (hcube c) v
    rw [pow_succ, pow_two, map_mul, map_mul] at h
    exact h
  have hx2 (x : Multiplicative (ZMod 2)) : x ^ 2 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    exact zmod2_two_nsmul x.toAdd
  have hxinv (x : Multiplicative (ZMod 2)) : x⁻¹ = x :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_two, hx2])
  have hvinv (v : A) : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by rw [← pow_two, h2])
  -- The three cosets.
  let g : Q ⧸ A := QuotientGroup.mk c
  have hg1 : g ≠ 1 := by
    intro h
    exact hc ((QuotientGroup.eq_one_iff c).mp h)
  have hc2 : c ^ 2 ∉ A := by
    intro h
    apply hc
    have h3 := hcube c
    have hc' : c = c ^ 3 * (c ^ 2)⁻¹ := by group
    rw [hc']
    exact A.mul_mem h3 (A.inv_mem h)
  have hg2 : g ^ 2 ≠ 1 := by
    intro h
    apply hc2
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact h
  have hgg : g ≠ g ^ 2 := by
    intro h
    apply hg1
    calc g = g ^ 2 * g⁻¹ := by group
      _ = g * g⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel g
  have huniv : (Finset.univ : Finset (Q ⧸ A)) = {1, g, g ^ 2} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem, Finset.card_pair hgg, ← Nat.card_eq_fintype_card, hindex]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hg1.symm, hg2.symm⟩
  have hclass (x : Q) : x ∈ A ∨ c⁻¹ * x ∈ A ∨ (c ^ 2)⁻¹ * x ∈ A := by
    have hx : (QuotientGroup.mk x : Q ⧸ A) ∈ (Finset.univ : Finset (Q ⧸ A)) :=
      Finset.mem_univ _
    rw [huniv] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx
    · exact Or.inl ((QuotientGroup.eq_one_iff x).mp hx)
    · exact Or.inr (Or.inl (QuotientGroup.eq.mp hx.symm))
    · refine Or.inr (Or.inr (QuotientGroup.eq.mp ?_))
      rw [QuotientGroup.mk_pow]
      exact hx.symm
  have hcomm : ∀ x y : Q, ⁅x, y⁆ ∈ A := by
    intro x y
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' A ⁅x, y⁆ = 1
    rw [map_commutatorElement]
    haveI : IsCyclic (Q ⧸ A) := isCyclic_of_prime_card hindex
    obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := Q ⧸ A)
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hz (QuotientGroup.mk' A x))
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hz (QuotientGroup.mk' A y))
    rw [← hi, ← hj, commutatorElement_def, (Commute.zpow_zpow_self z i j).eq]
    group
  let ℓ0 : A →* Multiplicative (ZMod 2) :=
    { toFun := fun v => ι v * ι (σ v) * ι (σ (σ v))
      map_one' := by simp
      map_mul' := fun v w => by
        simp only [map_mul]
        ac_rfl }
  have hconjpow (v : A) :
      MulAut.conjNormal (c ^ 2) v = σ (σ v) := by
    rw [pow_two, map_mul]
    rfl
  apply groupEpimorphism_card_le_coprimeSplitLabel 2 3 (by norm_num) A hA hcomm hcube ι ℓ0
  · intro v
    rw [huniv, Finset.sum_insert, Finset.sum_pair hgg]
    · have h1 : MulAut.conjNormal (Quotient.out (1 : Q ⧸ A) : Q) v = v := by
        apply conjNormal_self_of_mem A hA
        rw [← QuotientGroup.eq_one_iff]
        exact Quotient.out_eq _
      have hgc : MulAut.conjNormal (Quotient.out g : Q) v = σ v := by
        apply conjNormal_eq_of_mem A hA
        rw [← QuotientGroup.eq]
        exact (Quotient.out_eq _).symm
      have hg2c : MulAut.conjNormal (Quotient.out (g ^ 2) : Q) v = σ (σ v) := by
        rw [← hconjpow]
        apply conjNormal_eq_of_mem A hA
        rw [← QuotientGroup.eq, QuotientGroup.mk_pow]
        exact (Quotient.out_eq _).symm
      rw [h1, hgc, hg2c, hindex]
      change (ι v).toAdd + ((ι (σ v)).toAdd + (ι (σ (σ v))).toAdd) =
        (3 : ℕ) * (ι v * ι (σ v) * ι (σ (σ v))).toAdd
      rw [toAdd_mul, toAdd_mul]
      exact zmod2_average _ _ _
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hg1.symm, hg2.symm⟩
  · intro w hw1 hw0
    by_cases hwA : w ∈ A
    · let w' : A := ⟨w, hwA⟩
      have hcw1 : (⟨⁅w, c⁆, hcomm w c⟩ : A) = w' * (σ w')⁻¹ := by
        apply Subtype.ext
        simp [commutatorElement_def, hσapply, MulAut.conjNormal_apply, w', mul_assoc]
      have hcw2 : (⟨⁅w, c ^ 2⁆, hcomm w (c ^ 2)⟩ : A) = w' * (σ (σ w'))⁻¹ := by
        rw [← hconjpow w']
        apply Subtype.ext
        simp only [commutatorElement_def, MulAut.conjNormal_apply, Subgroup.coe_mul,
          Subgroup.coe_inv, w']
        group
      have e1 := hw1 c
      have e2 := hw1 (c ^ 2)
      rw [hcw1, map_mul, map_inv, hxinv] at e1
      rw [hcw2, map_mul, map_inv, hxinv] at e2
      have hw03 : (⟨w ^ 3, hcube w⟩ : A) = w' := by
        apply Subtype.ext
        change w ^ 3 = w
        have hw2 : w ^ 2 = 1 := congrArg Subtype.val (h2 w')
        calc w ^ 3 = w ^ 2 * w := pow_succ w 2
          _ = w := by rw [hw2, one_mul]
      rw [hw03] at hw0
      change ι w' * ι (σ w') * ι (σ (σ w')) = 1 at hw0
      have ha : ι (σ w') = ι w' := (inv_eq_of_mul_eq_one_right e1).symm.trans (hxinv _)
      have hb : ι (σ (σ w')) = ι w' :=
        (inv_eq_of_mul_eq_one_right e2).symm.trans (hxinv _)
      rw [ha, hb] at hw0
      have hι1 : ι w' = 1 := by
        calc ι w' = ι w' * ι w' * ι w' := by rw [← pow_two, hx2, one_mul]
          _ = 1 := hw0
      have hw'1 : w' = 1 := hι w' hι1 (by rw [← hσapply, ha, hι1])
        (by rw [← hσapply, ← hσapply, hb, hι1])
      exact congrArg Subtype.val hw'1
    · exfalso
      obtain ⟨v, hv⟩ := hσ
      have hτ : ∃ τ : A →* A, (∀ a : A, MulAut.conjNormal w a = τ a) ∧
          (∀ a : A, σ (τ a) = τ (σ a)) ∧ ((∀ a : A, τ a = a) → ∀ a : A, σ a = a) := by
        rcases (hclass w).resolve_left hwA with hw | hw
        · refine ⟨σ, fun a => conjNormal_eq_of_mem A hA hw a, fun a => rfl, fun h => h⟩
        · refine ⟨σ.comp σ, fun a => ?_, fun a => rfl, fun h a => ?_⟩
          · rw [conjNormal_eq_of_mem A hA hw a, hconjpow]
            rfl
          · exact (h (σ a)).symm.trans (hσ3 a)
      obtain ⟨τ, hconj, hcommτ, hτtriv⟩ := hτ
      have hu (a : A) : τ a * a⁻¹ = 1 := by
        have hca : (⟨⁅w, (a : Q)⁆, hcomm w a⟩ : A) = τ a * a⁻¹ := by
          rw [← hconj]
          apply Subtype.ext
          simp [commutatorElement_def, MulAut.conjNormal_apply]
        have e := hw1 a
        rw [hca] at e
        have hsig (b : A) : σ (τ b * b⁻¹) = τ (σ b) * (σ b)⁻¹ := by
          rw [map_mul, map_inv, hcommτ]
        have e' := hw1 (σ a)
        have hca' : (⟨⁅w, ((σ a : A) : Q)⁆, hcomm w (σ a)⟩ : A) = τ (σ a) * (σ a)⁻¹ := by
          rw [← hconj]
          apply Subtype.ext
          simp [commutatorElement_def, MulAut.conjNormal_apply]
        rw [hca'] at e'
        have e'' := hw1 (σ (σ a))
        have hca'' : (⟨⁅w, ((σ (σ a) : A) : Q)⁆, hcomm w (σ (σ a))⟩ : A) =
            τ (σ (σ a)) * (σ (σ a))⁻¹ := by
          rw [← hconj]
          apply Subtype.ext
          simp [commutatorElement_def, MulAut.conjNormal_apply]
        rw [hca''] at e''
        apply hι _ e
        · rw [← hσapply, hsig]
          exact e'
        · rw [← hσapply, ← hσapply, hsig, hsig]
          exact e''
      exact hv (hτtriv (fun a => mul_inv_eq_one.mp (hu a)) v)

end SymmetricSubgroupAsymptotics

end
