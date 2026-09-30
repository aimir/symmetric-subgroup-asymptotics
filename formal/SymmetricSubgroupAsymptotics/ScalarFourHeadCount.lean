import SymmetricSubgroupAsymptotics.BinaryTargetOrderEnvelope
import SymmetricSubgroupAsymptotics.JointSourceGraphs
import SymmetricSubgroupAsymptotics.EpimorphismKernelLabels

/-!
# Scalar `F₄` heads over index-three kernels

Let `θ : J ↠ C₃` with kernel `F`, and let `x ∈ J` map to the generator.
A homomorphism `ψ : F → F₄` is *twisted* when conjugation by `x` becomes
multiplication by a primitive cube root of unity `ω`.  Since `ω` has no
eigenvector in `F₂²`, a twisted map is determined by its first binary
coordinate, so there are at most `2^(d₂ F)` of them.

Different index-three kernels carrying nonzero twisted maps restrict to
jointly surjective maps on the derived subgroup `J'`.  Hence their number is
at most `d₂(J')/2`.  Together these bound onto maps to any quotient which is
an index-three extension of a central binary layer by copies of the natural
`F₄` module.  This is the counting core of the historical Y1 family.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical commutatorElement

namespace SymmetricSubgroupAsymptotics

/-! ## The natural module `F₄ = F₂²` -/

/-- `F₄` as a multiplicative group. -/
abbrev ScalarFour := Multiplicative (ZMod 2 × ZMod 2)

/-- Multiplication by a primitive cube root of unity. -/
def scalarFourOmegaAdd : ZMod 2 × ZMod 2 →+ ZMod 2 × ZMod 2 :=
  (AddMonoidHom.snd (ZMod 2) (ZMod 2)).prod
    (AddMonoidHom.fst (ZMod 2) (ZMod 2) + AddMonoidHom.snd (ZMod 2) (ZMod 2))

/-- Multiplication by `ω^c`. -/
def scalarFourTwistAdd (c : ZMod 3) : ZMod 2 × ZMod 2 →+ ZMod 2 × ZMod 2 :=
  if c = 0 then AddMonoidHom.id _
  else if c = 1 then scalarFourOmegaAdd
  else scalarFourOmegaAdd.comp scalarFourOmegaAdd

/-- Multiplication by `ω^c`, multiplicatively. -/
def scalarFourTwist (c : ZMod 3) : ScalarFour →* ScalarFour :=
  AddMonoidHom.toMultiplicative (scalarFourTwistAdd c)

/-- The first binary coordinate. -/
def scalarFourFst : ScalarFour →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative (AddMonoidHom.fst (ZMod 2) (ZMod 2))

private theorem twistAdd_add :
    ∀ (c d : ZMod 3) (v : ZMod 2 × ZMod 2),
      scalarFourTwistAdd (c + d) v =
        scalarFourTwistAdd c (scalarFourTwistAdd d v) := by
  unfold scalarFourTwistAdd scalarFourOmegaAdd
  decide

private theorem twistAdd_fixed :
    ∀ (c : ZMod 3) (v : ZMod 2 × ZMod 2),
      v ≠ 0 → scalarFourTwistAdd c v = v → c = 0 := by
  unfold scalarFourTwistAdd scalarFourOmegaAdd
  decide

private theorem twistAdd_span :
    ∀ v : ZMod 2 × ZMod 2, v ≠ 0 → ∀ u : ZMod 2 × ZMod 2,
      u = 0 ∨ u = v ∨ u = scalarFourTwistAdd 1 v ∨
        u = v + scalarFourTwistAdd 1 v := by
  unfold scalarFourTwistAdd scalarFourOmegaAdd
  decide

private theorem twistAdd_fst :
    ∀ u u' : ZMod 2 × ZMod 2, u.1 = u'.1 →
      (scalarFourTwistAdd 1 u).1 = (scalarFourTwistAdd 1 u').1 → u = u' := by
  unfold scalarFourTwistAdd scalarFourOmegaAdd
  decide

private theorem twistAdd_zero_eq : ∀ v : ZMod 2 × ZMod 2,
    scalarFourTwistAdd 0 v = v := by
  unfold scalarFourTwistAdd scalarFourOmegaAdd
  decide

theorem scalarFourTwist_add (c d : ZMod 3) (v : ScalarFour) :
    scalarFourTwist (c + d) v = scalarFourTwist c (scalarFourTwist d v) :=
  twistAdd_add c d (Multiplicative.toAdd v)

theorem scalarFourTwist_zero (v : ScalarFour) : scalarFourTwist 0 v = v :=
  twistAdd_zero_eq (Multiplicative.toAdd v)

/-- `ω^c` fixes a nonzero vector only for `c = 0`. -/
theorem scalarFourTwist_fixed {c : ZMod 3} {v : ScalarFour} (hv : v ≠ 1)
    (h : scalarFourTwist c v = v) : c = 0 :=
  twistAdd_fixed c (Multiplicative.toAdd v)
    (fun h0 => hv (by simpa using congrArg Multiplicative.ofAdd h0)) h

/-- An `ω`-stable subgroup of `F₄` containing a nonzero vector is
everything. -/
theorem scalarFour_stable_eq_top (A : Subgroup ScalarFour)
    (hA : ∀ v ∈ A, scalarFourTwist 1 v ∈ A) {v : ScalarFour} (hv : v ∈ A)
    (hv1 : v ≠ 1) : A = ⊤ := by
  rw [eq_top_iff]
  intro u _
  have hv0 : Multiplicative.toAdd v ≠ 0 :=
    fun h0 => hv1 (by simpa using congrArg Multiplicative.ofAdd h0)
  rcases twistAdd_span (Multiplicative.toAdd v) hv0 (Multiplicative.toAdd u) with
    h | h | h | h
  · have : u = 1 := by simpa using congrArg Multiplicative.ofAdd h
    rw [this]
    exact A.one_mem
  · have : u = v := by simpa using congrArg Multiplicative.ofAdd h
    rw [this]
    exact hv
  · have : u = scalarFourTwist 1 v := by
      simpa [scalarFourTwist] using congrArg Multiplicative.ofAdd h
    rw [this]
    exact hA v hv
  · have : u = v * scalarFourTwist 1 v := by
      simpa [scalarFourTwist] using congrArg Multiplicative.ofAdd h
    rw [this]
    exact A.mul_mem hv (hA v hv)

/-- A vector is determined by the first coordinates of itself and of its
`ω`-image. -/
theorem scalarFour_eq_of_fst {u u' : ScalarFour}
    (h₁ : scalarFourFst u = scalarFourFst u')
    (h₂ : scalarFourFst (scalarFourTwist 1 u) =
      scalarFourFst (scalarFourTwist 1 u')) : u = u' := by
  have := twistAdd_fst (Multiplicative.toAdd u) (Multiplicative.toAdd u')
    (congrArg Multiplicative.toAdd h₁) (congrArg Multiplicative.toAdd h₂)
  simpa using congrArg Multiplicative.ofAdd this

/-! ## Twisted homomorphisms -/

/-- Twisted maps are determined by their first binary coordinate. -/
theorem twistedHom_eq_of_fst {F : Type*} [Group F] (α : F → F)
    {ψ ψ' : F →* ScalarFour}
    (hψ : ∀ f, ψ (α f) = scalarFourTwist 1 (ψ f))
    (hψ' : ∀ f, ψ' (α f) = scalarFourTwist 1 (ψ' f))
    (h : scalarFourFst.comp ψ = scalarFourFst.comp ψ') : ψ = ψ' := by
  ext1 f
  apply scalarFour_eq_of_fst (DFunLike.congr_fun h f)
  rw [← hψ, ← hψ']
  exact DFunLike.congr_fun h (α f)

/-- There are at most `2^(d₂ F)` twisted maps. -/
theorem twistedHom_card_le {F : Type*} [Group F] [Finite F] (α : F → F)
    (S : Set (F →* ScalarFour))
    (hS : ∀ ψ ∈ S, ∀ f, ψ (α f) = scalarFourTwist 1 (ψ f)) :
    Nat.card S ≤ 2 ^ binaryCharacterRank F := by
  have hinj : Function.Injective
      (fun ψ : S => scalarFourFst.comp ψ.1) := by
    intro ψ ψ' h
    exact Subtype.ext (twistedHom_eq_of_fst α (hS ψ.1 ψ.2) (hS ψ'.1 ψ'.2) h)
  letI : Finite (F →* Multiplicative (ZMod 2)) :=
    Finite.of_injective (fun f : F →* Multiplicative (ZMod 2) =>
      (f : F → Multiplicative (ZMod 2))) DFunLike.coe_injective
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [binaryAbelianizationGroupHom_card] at hcard
  simpa using hcard


/-! ## Heads over index-three kernels -/

/-- The cyclic target of an index-three top. -/
abbrev CyclicThree := Multiplicative (ZMod 3)

/-- Two index-three tops of the same finite group have kernels of the same
order. -/
theorem cyclicThree_ker_card_eq {J : Type*} [Group J] [Finite J]
    (θ θ' : J →* CyclicThree) (hθ : Function.Surjective θ)
    (hθ' : Function.Surjective θ') :
    Nat.card θ.ker = Nat.card θ'.ker := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker
  have h' := Subgroup.card_eq_card_quotient_mul_card_subgroup θ'.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hθ).toEquiv]
    at h
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ' hθ').toEquiv]
    at h'
  have hpos : 0 < Nat.card CyclicThree := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h.symm.trans h')

/-- An index-three quotient whose kernel carries a nonzero twisted `F₄`
map: conjugation by `g` acts as `ω^θ(g)`. -/
structure ScalarFourHead (J : Type*) [Group J] where
  top : J →* CyclicThree
  top_surjective : Function.Surjective top
  map : top.ker →* ScalarFour
  twisted : ∀ (g : J) (f : top.ker),
    map (MulAut.conjNormal g f) =
      scalarFourTwist (Multiplicative.toAdd (top g)) (map f)
  map_ne_one : map ≠ 1

namespace ScalarFourHead

variable {J : Type*} [Group J] (H : ScalarFourHead J)

theorem commutator_le_ker : commutator J ≤ H.top.ker :=
  Abelianization.commutator_subset_ker H.top

/-- The restriction of the head map to the derived subgroup. -/
def derived : commutator J →* ScalarFour :=
  H.map.comp (Subgroup.inclusion H.commutator_le_ker)

theorem derived_twisted (g : J) (k : commutator J) :
    H.derived (MulAut.conjNormal g k) =
      scalarFourTwist (Multiplicative.toAdd (H.top g)) (H.derived k) := by
  have hinc : Subgroup.inclusion H.commutator_le_ker (MulAut.conjNormal g k) =
      MulAut.conjNormal g (Subgroup.inclusion H.commutator_le_ker k) :=
    Subtype.ext rfl
  change H.map (Subgroup.inclusion H.commutator_le_ker (MulAut.conjNormal g k)) = _
  rw [hinc, H.twisted]
  rfl

/-- A nonzero twisted map is nonzero on the derived subgroup: modulo `J'`
conjugation by a generator is trivial, while `ω` fixes no nonzero vector. -/
theorem derived_ne_one : H.derived ≠ 1 := by
  intro h
  apply H.map_ne_one
  obtain ⟨x, hx⟩ := H.top_surjective (Multiplicative.ofAdd 1)
  refine MonoidHom.ext fun f => ?_
  have hcomm : ⁅x, (f : J)⁆ ∈ commutator J :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top x)
      (Subgroup.mem_top _)
  have hsplit : MulAut.conjNormal x f =
      Subgroup.inclusion H.commutator_le_ker ⟨_, hcomm⟩ * f := by
    apply Subtype.ext
    simp only [MulAut.conjNormal_apply, Subgroup.coe_mul,
      Subgroup.coe_inclusion, commutatorElement_def]
    group
  have h1 : H.map (MulAut.conjNormal x f) = H.map f := by
    rw [hsplit, map_mul]
    have h0 : H.map (Subgroup.inclusion H.commutator_le_ker ⟨_, hcomm⟩) = 1 :=
      DFunLike.congr_fun h ⟨_, hcomm⟩
    rw [h0, one_mul]
  have h2 := H.twisted x f
  rw [h1, hx] at h2
  change H.map f = 1
  by_contra hne
  have h3 := scalarFourTwist_fixed hne h2.symm
  exact absurd h3 (by decide)

end ScalarFourHead

/-- Heads with distinct kernels restrict to jointly surjective maps on the
derived subgroup.  A nonsurjective step would force a twisted map between
two heads, and hence an inclusion of their index-three kernels. -/
theorem scalarFourHeads_jointly_surjective {J : Type*} [Group J] [Finite J]
    {ι : Type*} [DecidableEq ι] (H : ι → ScalarFourHead J)
    (hdistinct : Pairwise fun i j => (H i).top.ker ≠ (H j).top.ker)
    (s : Finset ι) :
    ∀ v : ι → ScalarFour, ∃ k : commutator J,
      ∀ i ∈ s, (H i).derived k = v i := by
  induction s using Finset.induction_on with
  | empty => exact fun _ => ⟨1, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert j t hjt ih =>
    -- Elements with the same values on `t`.
    let K : Subgroup (commutator J) := ⨅ i ∈ t, ((H i).derived).ker
    have hK : ∀ k, k ∈ K ↔ ∀ i ∈ t, (H i).derived k = 1 := by
      intro k
      simp only [K, Subgroup.mem_iInf, MonoidHom.mem_ker]
    have hKconj : ∀ (g : J) (k : commutator J), k ∈ K →
        MulAut.conjNormal g k ∈ K := by
      intro g k hk
      rw [hK] at hk ⊢
      intro i hi
      rw [(H i).derived_twisted, hk i hi, map_one]
    let A : Subgroup ScalarFour := K.map (H j).derived
    have hA : A = ⊤ := by
      by_contra hne
      have hkill : ∀ k ∈ K, (H j).derived k = 1 := by
        intro k hk
        by_contra hk1
        apply hne
        refine scalarFour_stable_eq_top A ?_ ⟨k, hk, rfl⟩ hk1
        rintro v ⟨k', hk', rfl⟩
        obtain ⟨g, hg⟩ := (H j).top_surjective (Multiplicative.ofAdd 1)
        refine ⟨MulAut.conjNormal g k', hKconj g k' hk', ?_⟩
        rw [(H j).derived_twisted, hg]
        rfl
      have hsame : ∀ k k' : commutator J,
          (∀ i ∈ t, (H i).derived k = (H i).derived k') →
            (H j).derived k = (H j).derived k' := by
        intro k k' hkk
        have hmem : k⁻¹ * k' ∈ K := by
          rw [hK]
          intro i hi
          rw [map_mul, map_inv, hkk i hi, inv_mul_cancel]
        have := hkill _ hmem
        rw [map_mul, map_inv] at this
        exact (inv_mul_eq_one.mp this)
      choose c hc using ih
      let f : (ι → ScalarFour) →* ScalarFour :=
        { toFun := fun v => (H j).derived (c v)
          map_one' := by
            change (H j).derived (c 1) = 1
            rw [← (H j).derived.map_one]
            apply hsame
            intro i hi
            rw [hc 1 i hi, map_one]
            rfl
          map_mul' := by
            intro v v'
            change (H j).derived (c (v * v')) =
              (H j).derived (c v) * (H j).derived (c v')
            rw [← map_mul]
            apply hsame
            intro i hi
            rw [hc _ i hi, map_mul, hc v i hi, hc v' i hi]
            rfl }
      have hf : ∀ k : commutator J,
          f (fun i => (H i).derived k) = (H j).derived k := by
        intro k
        apply hsame
        intro i hi
        exact hc _ i hi
      have hft : ∀ v v' : ι → ScalarFour, (∀ i ∈ t, v i = v' i) →
          f v = f v' := by
        intro v v' hvv
        apply hsame
        intro i hi
        rw [hc v i hi, hc v' i hi, hvv i hi]
      obtain ⟨k₀, hk₀⟩ : ∃ k₀, (H j).derived k₀ ≠ 1 := by
        by_contra hall
        push Not at hall
        exact (H j).derived_ne_one (MonoidHom.ext hall)
      let w : ι → ScalarFour := fun i => (H i).derived k₀
      have hprod : f w = ∏ i ∈ t, f (Pi.mulSingle i (w i)) := by
        rw [← map_prod]
        apply hft
        intro l hl
        rw [Finset.prod_apply]
        simp [hl]
      have hfw : f w ≠ 1 := by
        rw [hf]
        exact hk₀
      obtain ⟨i, hi, hne1⟩ : ∃ i ∈ t, f (Pi.mulSingle i (w i)) ≠ 1 := by
        by_contra hall
        push Not at hall
        exact hfw (hprod.trans (Finset.prod_eq_one hall))
      have hij : i ≠ j := fun h => hjt (h ▸ hi)
      let e : ι → ScalarFour := Pi.mulSingle i (w i)
      let k := c e
      have hle : (H i).top.ker ≤ (H j).top.ker := by
        intro g hg
        rw [MonoidHom.mem_ker] at hg ⊢
        have hk' : (H j).derived (MulAut.conjNormal g k) = (H j).derived k := by
          apply hsame
          intro l hl
          rw [(H l).derived_twisted, hc e l hl]
          by_cases hli : l = i
          · subst hli
            rw [hg]
            simp [e, scalarFourTwist_zero]
          · simp [e, hli]
        rw [(H j).derived_twisted] at hk'
        have hkne : (H j).derived k ≠ 1 := hne1
        have h0 := scalarFourTwist_fixed hkne hk'
        simpa using congrArg Multiplicative.ofAdd h0
      have heq : (H i).top.ker = (H j).top.ker :=
        Subgroup.eq_of_le_of_card_ge hle
          (cyclicThree_ker_card_eq _ _ (H j).top_surjective
            (H i).top_surjective).le
      exact hdistinct hij heq
    intro v
    obtain ⟨k₁, hk₁⟩ := ih v
    have hmem : ((H j).derived k₁)⁻¹ * v j ∈ A := by
      rw [hA]
      exact Subgroup.mem_top _
    obtain ⟨k₂, hk₂K, hk₂⟩ := hmem
    refine ⟨k₁ * k₂, ?_⟩
    intro l hl
    rcases Finset.mem_insert.mp hl with hlj | hlt
    · subst hlj
      rw [map_mul, hk₂, mul_inv_cancel_left]
    · rw [map_mul, hk₁ l hlt, (hK k₂).mp hk₂K l hlt, mul_one]

/-- The binary pairing `F₂² → F₂` with a fixed vector. -/
def scalarFourDotAdd (t : ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 →+ ZMod 2 where
  toFun u := t.1 * u.1 + t.2 * u.2
  map_zero' := by simp
  map_add' u u' := by simp only [Prod.fst_add, Prod.snd_add]; ring

private theorem scalarFourDotAdd_injective :
    ∀ t t' : ZMod 2 × ZMod 2,
      (∀ u : ZMod 2 × ZMod 2, scalarFourDotAdd t u = scalarFourDotAdd t' u) →
        t = t' := by
  unfold scalarFourDotAdd
  decide

/-- The pairing, multiplicatively. -/
def scalarFourDot (t : ZMod 2 × ZMod 2) : ScalarFour →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative (scalarFourDotAdd t)

/-- Heads with pairwise distinct kernels number at most `d₂(J')/2`. -/
theorem scalarFourHeads_card_le {J : Type*} [Group J] [Finite J]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (H : ι → ScalarFourHead J)
    (hdistinct : Pairwise fun i j => (H i).top.ker ≠ (H j).top.ker) :
    2 * Fintype.card ι ≤ binaryCharacterRank (commutator J) := by
  have hsurj := scalarFourHeads_jointly_surjective H hdistinct Finset.univ
  let χ : (ι → ZMod 2 × ZMod 2) → (commutator J →* Multiplicative (ZMod 2)) :=
    fun s => ∏ i, (scalarFourDot (s i)).comp (H i).derived
  have hχ : Function.Injective χ := by
    intro s s' h
    funext i
    apply scalarFourDotAdd_injective
    intro u
    obtain ⟨k, hk⟩ := hsurj (Pi.mulSingle i (Multiplicative.ofAdd u))
    have hval := DFunLike.congr_fun h k
    simp only [χ, MonoidHom.finsetProd_apply, MonoidHom.comp_apply] at hval
    rw [Finset.prod_eq_single i, Finset.prod_eq_single i] at hval
    · rw [hk i (Finset.mem_univ i)] at hval
      simpa [scalarFourDot] using congrArg Multiplicative.toAdd hval
    all_goals first
      | (intro l _ hl
         rw [hk l (Finset.mem_univ l), Pi.mulSingle_eq_of_ne hl, map_one])
      | (intro hi; exact absurd (Finset.mem_univ i) hi)
  letI : Finite (commutator J →* Multiplicative (ZMod 2)) :=
    Finite.of_injective (fun f : commutator J →* Multiplicative (ZMod 2) =>
      (f : commutator J → Multiplicative (ZMod 2))) DFunLike.coe_injective
  have hcard := Nat.card_le_card_of_injective χ hχ
  rw [binaryAbelianizationGroupHom_card, Nat.card_fun, Nat.card_prod,
    Nat.card_zmod, Nat.card_eq_fintype_card] at hcard
  simp only [Module.finrank_self, mul_one] at hcard
  have h4 : (2 * 2) ^ Fintype.card ι = 2 ^ (2 * Fintype.card ι) := by
    rw [pow_mul]
    norm_num
  rw [h4] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hcard


/-! ## Counting through fibres -/

/-- A map whose fibres have at most `M` elements. -/
theorem natCard_le_mul_of_fibre {X Y : Type*} [Finite X] [Finite Y] (π : X → Y)
    (M : ℕ) (h : ∀ y, Nat.card {x // π x = y} ≤ M) :
    Nat.card X ≤ Nat.card Y * M := by
  letI := Fintype.ofFinite Y
  letI : ∀ y, Finite {x // π x = y} := fun _ => inferInstance
  calc Nat.card X = Nat.card (Σ y, {x // π x = y}) :=
        (Nat.card_congr (Equiv.sigmaFiberEquiv π)).symm
    _ = ∑ y, Nat.card {x // π x = y} := Nat.card_sigma
    _ ≤ ∑ _y : Y, M := Finset.sum_le_sum (fun y _ => h y)
    _ = Nat.card Y * M := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
          Nat.card_eq_fintype_card]

/-- The cyclic group of order three has at most two automorphisms. -/
theorem cyclicThree_aut_card_le : Nat.card (CyclicThree ≃* CyclicThree) ≤ 2 := by
  let g : CyclicThree := Multiplicative.ofAdd 1
  have hgen : ∀ c : CyclicThree, c = g ^ (Multiplicative.toAdd c).val := by
    decide
  let e : (CyclicThree ≃* CyclicThree) → {c : CyclicThree // c ≠ 1} :=
    fun α => ⟨α g, fun h => by
      have : g = 1 := α.injective (h.trans α.map_one.symm)
      exact absurd this (by decide)⟩
  have he : Function.Injective e := by
    intro α β h
    apply MulEquiv.ext
    intro c
    have hαβ : α g = β g := congrArg Subtype.val h
    rw [hgen c, map_pow, map_pow, hαβ]
  have hcard : Nat.card {c : CyclicThree // c ≠ 1} = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  letI : Finite (CyclicThree ≃* CyclicThree) :=
    Finite.of_injective e he
  exact (Nat.card_le_card_of_injective e he).trans hcard.le

/-! ## Index-three extensions of a central binary layer by `F₄` layers -/

/-- A quotient `Q` with an index-three top whose kernel `P` has a central
binary subgroup `Z` and coordinates `P → F₄` with joint kernel `Z`, each
twisted by the top.  The first coordinate is onto. -/
structure ScalarFourHeadedQuotient (Q : Type) [Group Q] where
  top : Q →* CyclicThree
  top_surjective : Function.Surjective top
  center : Subgroup top.ker
  center_comm : ∀ z ∈ center, ∀ p : top.ker, z * p = p * z
  center_twoGroup : IsPGroup 2 center
  layers : ℕ
  coord : Fin (layers + 1) → (top.ker →* ScalarFour)
  coord_center : ∀ j, ∀ z ∈ center, coord j z = 1
  coord_joint : ∀ p : top.ker, (∀ j, coord j p = 1) → p ∈ center
  coord_twisted : ∀ (q : Q) (p : top.ker) j,
    coord j (MulAut.conjNormal q p) =
      scalarFourTwist (Multiplicative.toAdd (top q)) (coord j p)
  coord_zero_surjective : Function.Surjective (coord 0)

namespace ScalarFourHeadedQuotient

variable {Q : Type} [Group Q] (h : ScalarFourHeadedQuotient Q)

/-- The binary exponent per unit of `d₂` of an index-three kernel. -/
def weight : ℕ := (h.layers + 1) + Nat.log 2 (Nat.card h.center)

variable {J : Type*} [Group J] [Finite J] [Finite Q]

/-- The restriction of an onto map to the kernel of its top. -/
def kernelRestriction (φ : GroupEpimorphism J Q) :
    (h.top.comp φ.1).ker →* h.top.ker :=
  (φ.1.comp (h.top.comp φ.1).ker.subtype).codRestrict h.top.ker (by
    intro f
    exact f.2)

omit [Finite J] [Finite Q] in
theorem kernelRestriction_surjective (φ : GroupEpimorphism J Q) :
    Function.Surjective (h.kernelRestriction φ) := by
  intro p
  obtain ⟨g, hg⟩ := φ.2 (p : Q)
  have hgker : g ∈ (h.top.comp φ.1).ker := by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hg]
    exact p.2
  exact ⟨⟨g, hgker⟩, Subtype.ext hg⟩

omit [Finite J] [Finite Q] in
theorem kernelRestriction_twisted (φ : GroupEpimorphism J Q) (g : J)
    (f : (h.top.comp φ.1).ker) (j : Fin (h.layers + 1)) :
    h.coord j (h.kernelRestriction φ (MulAut.conjNormal g f)) =
      scalarFourTwist (Multiplicative.toAdd (h.top.comp φ.1 g))
        (h.coord j (h.kernelRestriction φ f)) := by
  have heq : h.kernelRestriction φ (MulAut.conjNormal g f) =
      MulAut.conjNormal (φ.1 g) (h.kernelRestriction φ f) := by
    apply Subtype.ext
    simp [kernelRestriction]
  rw [heq, h.coord_twisted]
  rfl

/-- The head of an onto map, on the first coordinate. -/
def head (φ : GroupEpimorphism J Q) : ScalarFourHead J where
  top := h.top.comp φ.1
  top_surjective := h.top_surjective.comp φ.2
  map := (h.coord 0).comp (h.kernelRestriction φ)
  twisted g f := h.kernelRestriction_twisted φ g f 0
  map_ne_one := by
    intro h1
    obtain ⟨p, hp⟩ := h.coord_zero_surjective (Multiplicative.ofAdd (1, 0))
    obtain ⟨f, hf⟩ := h.kernelRestriction_surjective φ p
    have := DFunLike.congr_fun h1 f
    simp only [MonoidHom.comp_apply, hf, hp, MonoidHom.one_apply] at this
    exact absurd this (by decide)

/-- Onto maps over one fixed top: at most `|Q| 2^(weight · d₂ F)`. -/
theorem fibre_card_le (θ : J →* CyclicThree) (hθ : Function.Surjective θ) :
    Nat.card {φ : GroupEpimorphism J Q // h.top.comp φ.1 = θ} ≤
      Nat.card Q * 2 ^ (h.weight * binaryCharacterRank θ.ker) := by
  obtain ⟨x, hx⟩ := hθ (Multiplicative.ofAdd 1)
  let F := θ.ker
  -- restriction to the fixed kernel `F`
  let restr : {φ : GroupEpimorphism J Q // h.top.comp φ.1 = θ} →
      (F →* h.top.ker) := fun φ =>
    (φ.1.1.comp F.subtype).codRestrict h.top.ker (by
      intro f
      have := DFunLike.congr_fun φ.2 (f : J)
      simp only [MonoidHom.comp_apply] at this
      rw [MonoidHom.mem_ker]
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, this]
      exact f.2)
  -- a generator image and the restriction determine the map
  have hdet : Function.Injective
      (fun φ : {φ : GroupEpimorphism J Q // h.top.comp φ.1 = θ} =>
        (φ.1.1 x, restr φ)) := by
    intro φ ψ hφψ
    simp only [Prod.mk.injEq] at hφψ
    obtain ⟨hx', hr⟩ := hφψ
    apply Subtype.ext
    apply Subtype.ext
    ext g
    let m := (Multiplicative.toAdd (θ g)).val
    have hmem : (x ^ m)⁻¹ * g ∈ F := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hx]
      have hm : (Multiplicative.ofAdd (1 : ZMod 3)) ^ m = θ g := by
        rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one]
        simp [m]
      rw [hm, inv_mul_cancel]
    have hf := congrArg Subtype.val (DFunLike.congr_fun hr ⟨_, hmem⟩)
    change φ.1.1 ((x ^ m)⁻¹ * g) = ψ.1.1 ((x ^ m)⁻¹ * g) at hf
    rw [map_mul, map_mul, map_inv, map_inv, map_pow, map_pow, hx'] at hf
    exact mul_left_cancel hf
  -- the restrictions are twisted
  let T : Set (F →* h.top.ker) := {ρ | ∀ j f,
    h.coord j (ρ (MulAut.conjNormal x f)) = scalarFourTwist 1 (h.coord j (ρ f))}
  have hT : ∀ φ, restr φ ∈ T := by
    intro φ j f
    have heq : restr φ (MulAut.conjNormal x f) =
        MulAut.conjNormal (φ.1.1 x) (restr φ f) := by
      apply Subtype.ext
      simp [restr]
    rw [heq, h.coord_twisted]
    have hxq : h.top (φ.1.1 x) = Multiplicative.ofAdd 1 := by
      have := DFunLike.congr_fun φ.2 x
      simp only [MonoidHom.comp_apply] at this
      rw [this, hx]
    rw [hxq]
    rfl
  -- count the twisted restrictions through their binary first coordinates
  let π : T → (Fin (h.layers + 1) → (F →* Multiplicative (ZMod 2))) :=
    fun ρ j => scalarFourFst.comp ((h.coord j).comp ρ.1)
  letI : Finite (F →* h.top.ker) := Finite.of_injective
    (fun ρ : F →* h.top.ker => (ρ : F → h.top.ker)) DFunLike.coe_injective
  letI : Finite (F →* Multiplicative (ZMod 2)) := Finite.of_injective
    (fun ρ : F →* Multiplicative (ZMod 2) => (ρ : F → Multiplicative (ZMod 2)))
    DFunLike.coe_injective
  letI : Finite (F →* h.center) := Finite.of_injective
    (fun ρ : F →* h.center => (ρ : F → h.center)) DFunLike.coe_injective
  have hfibre : ∀ y, Nat.card {ρ // π ρ = y} ≤ Nat.card (F →* h.center) := by
    intro y
    by_cases hne : Nonempty {ρ // π ρ = y}
    · obtain ⟨ρ₀⟩ := hne
      -- two restrictions in one fibre have equal coordinates
      have hcoord : ∀ ρ : {ρ // π ρ = y}, ∀ j,
          (h.coord j).comp ρ.1.1 = (h.coord j).comp ρ₀.1.1 := by
        intro ρ j
        apply twistedHom_eq_of_fst (fun f => MulAut.conjNormal x f)
          (fun f => ρ.1.2 j f) (fun f => ρ₀.1.2 j f)
        exact (congrFun ρ.2 j).trans (congrFun ρ₀.2 j).symm
      have hdiff : ∀ (ρ : {ρ // π ρ = y}) (f : F),
          ρ.1.1 f * (ρ₀.1.1 f)⁻¹ ∈ h.center := by
        intro ρ f
        apply h.coord_joint
        intro j
        have := DFunLike.congr_fun (hcoord ρ j) f
        simp only [MonoidHom.comp_apply] at this
        rw [map_mul, map_inv, this, mul_inv_cancel]
      let δ : {ρ // π ρ = y} → (F →* h.center) := fun ρ =>
        { toFun := fun f => ⟨ρ.1.1 f * (ρ₀.1.1 f)⁻¹, hdiff ρ f⟩
          map_one' := by
            apply Subtype.ext
            simp
          map_mul' := by
            intro f f'
            apply Subtype.ext
            have hc : Commute (ρ.1.1 f' * (ρ₀.1.1 f')⁻¹) (ρ₀.1.1 f) :=
              h.center_comm _ (hdiff ρ f') (ρ₀.1.1 f)
            have hc' := hc.inv_right
            simp only [map_mul, Subgroup.coe_mul, mul_inv_rev]
            calc ρ.1.1 f * ρ.1.1 f' * ((ρ₀.1.1 f')⁻¹ * (ρ₀.1.1 f)⁻¹)
                = ρ.1.1 f * ((ρ.1.1 f' * (ρ₀.1.1 f')⁻¹) * (ρ₀.1.1 f)⁻¹) := by
                  group
              _ = ρ.1.1 f * ((ρ₀.1.1 f)⁻¹ * (ρ.1.1 f' * (ρ₀.1.1 f')⁻¹)) := by
                  rw [hc'.eq]
              _ = ρ.1.1 f * (ρ₀.1.1 f)⁻¹ * (ρ.1.1 f' * (ρ₀.1.1 f')⁻¹) := by
                  group }
      have hδ : Function.Injective δ := by
        intro ρ ρ' hρ
        apply Subtype.ext
        apply Subtype.ext
        ext1 f
        have := congrArg Subtype.val (DFunLike.congr_fun hρ f)
        change ρ.1.1 f * (ρ₀.1.1 f)⁻¹ = ρ'.1.1 f * (ρ₀.1.1 f)⁻¹ at this
        exact mul_right_cancel this
      exact Nat.card_le_card_of_injective δ hδ
    · rw [not_nonempty_iff] at hne
      rw [Nat.card_of_isEmpty]
      exact Nat.zero_le _
  have hTcard := natCard_le_mul_of_fibre π _ hfibre
  have hZ : Nat.card (F →* h.center) ≤
      2 ^ (Nat.log 2 (Nat.card h.center) * binaryCharacterRank F) :=
    binaryTargetOrder_hom_card_le h.center_twoGroup
  have hC2 : Nat.card (F →* Multiplicative (ZMod 2)) = 2 ^ binaryCharacterRank F := by
    rw [binaryAbelianizationGroupHom_card]
    simp
  have hTbound : Nat.card T ≤
      2 ^ (h.weight * binaryCharacterRank F) := by
    calc Nat.card T ≤ Nat.card (Fin (h.layers + 1) → (F →* Multiplicative (ZMod 2))) *
          Nat.card (F →* h.center) := hTcard
      _ ≤ (2 ^ binaryCharacterRank F) ^ (h.layers + 1) *
          2 ^ (Nat.log 2 (Nat.card h.center) * binaryCharacterRank F) := by
          rw [Nat.card_fun, hC2, Nat.card_fin]
          exact Nat.mul_le_mul_left _ hZ
      _ = 2 ^ (h.weight * binaryCharacterRank F) := by
          rw [← pow_mul, ← pow_add]
          congr 1
          unfold weight
          ring
  let restrT : {φ : GroupEpimorphism J Q // h.top.comp φ.1 = θ} → Q × T :=
    fun φ => (φ.1.1 x, ⟨restr φ, hT φ⟩)
  have hrestrT : Function.Injective restrT := by
    intro φ ψ hφψ
    apply hdet
    simp only [restrT, Prod.mk.injEq, Subtype.mk.injEq] at hφψ
    simp [hφψ.1, hφψ.2]
  calc Nat.card {φ : GroupEpimorphism J Q // h.top.comp φ.1 = θ}
      ≤ Nat.card (Q × T) := Nat.card_le_card_of_injective restrT hrestrT
    _ = Nat.card Q * Nat.card T := Nat.card_prod _ _
    _ ≤ Nat.card Q * 2 ^ (h.weight * binaryCharacterRank F) :=
        Nat.mul_le_mul_left _ hTbound


/-- The index-three tops realised by onto maps number at most `d₂(J')`. -/
theorem realisedTops_card_le :
    Nat.card (Set.range fun φ : GroupEpimorphism J Q => h.top.comp φ.1) ≤
      binaryCharacterRank (commutator J) := by
  let R := Set.range fun φ : GroupEpimorphism J Q => h.top.comp φ.1
  letI : Finite (GroupEpimorphism J Q) := Finite.of_injective
    (fun φ : GroupEpimorphism J Q => (φ.1 : J → Q))
    (fun _ _ hφ => Subtype.ext (DFunLike.coe_injective hφ))
  letI : Finite R := Set.finite_range _ |>.to_subtype
  let κ : R → Subgroup J := fun θ => θ.1.ker
  let T := Set.range κ
  letI : Finite T := Set.finite_range _ |>.to_subtype
  letI : Fintype T := Fintype.ofFinite T
  -- kernels determine tops up to the two automorphisms of `C₃`
  have hfib : ∀ K : T, Nat.card {θ : R // κ θ = K} ≤ 2 := by
    intro K
    obtain ⟨θ₀, hθ₀⟩ := K.2
    obtain ⟨φ₀, hφ₀⟩ := θ₀.2
    let e₀ : GroupEpimorphism J CyclicThree :=
      ⟨θ₀.1, by rw [← hφ₀]; exact h.top_surjective.comp φ₀.2⟩
    let ι : {θ : R // κ θ = K} →
        {g : GroupEpimorphism J CyclicThree // g.1.ker = e₀.1.ker} :=
      fun θ => ⟨⟨θ.1.1, by
        obtain ⟨φ, hφ⟩ := θ.1.2
        rw [← hφ]
        exact h.top_surjective.comp φ.2⟩, by
        change θ.1.1.ker = θ₀.1.ker
        exact θ.2.trans hθ₀.symm⟩
    have hι : Function.Injective ι := by
      intro θ θ' hθ
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun g => g.1.1) hθ
    letI : Finite (GroupEpimorphism J CyclicThree) := Finite.of_injective
      (fun g : GroupEpimorphism J CyclicThree => (g.1 : J → CyclicThree))
      (fun _ _ hg => Subtype.ext (DFunLike.coe_injective hg))
    calc Nat.card {θ : R // κ θ = K}
        ≤ Nat.card {g : GroupEpimorphism J CyclicThree // g.1.ker = e₀.1.ker} :=
          Nat.card_le_card_of_injective ι hι
      _ = Nat.card (CyclicThree ≃* CyclicThree) :=
          groupEpimorphism_kernel_fibre_card e₀
      _ ≤ 2 := cyclicThree_aut_card_le
  have hRT : Nat.card R ≤ Nat.card T * 2 :=
    natCard_le_mul_of_fibre (fun θ : R => (⟨κ θ, θ, rfl⟩ : T)) 2 (by
      intro K
      refine le_trans ?_ (hfib K)
      apply Nat.card_le_card_of_injective
        (fun θ => (⟨θ.1, congrArg Subtype.val θ.2⟩ : {θ : R // κ θ = K}))
      intro θ θ' hθ
      simp only [Subtype.mk.injEq] at hθ
      exact Subtype.ext hθ)
  -- one head for each realised kernel
  have hwit : ∀ K : T, ∃ φ : GroupEpimorphism J Q, (h.top.comp φ.1).ker = K := by
    intro K
    obtain ⟨θ, hθ⟩ := K.2
    obtain ⟨φ, hφ⟩ := θ.2
    exact ⟨φ, (congrArg MonoidHom.ker hφ).trans hθ⟩
  choose φ hφ using hwit
  have hheads := scalarFourHeads_card_le (fun K : T => h.head (φ K)) (by
    intro K K' hKK' heq
    apply hKK'
    apply Subtype.ext
    exact (hφ K).symm.trans (heq.trans (hφ K')))
  rw [Fintype.card_eq_nat_card] at hheads
  show Nat.card R ≤ _
  omega

/-- Onto maps to a headed quotient, when every index-three kernel of the
complete source has `d₂ ≤ d`:
`Epi(J, Q) ≤ d₂(J') |Q| 2^(weight · d)`. -/
theorem epi_card_le (d : ℝ)
    (hd : ∀ θ : J →* CyclicThree, Function.Surjective θ →
      (binaryCharacterRank θ.ker : ℝ) ≤ d) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      binaryCharacterRank (commutator J) * Nat.card Q *
        (2 : ℝ) ^ ((h.weight : ℝ) * d) := by
  letI : Finite (GroupEpimorphism J Q) := Finite.of_injective
    (fun φ : GroupEpimorphism J Q => (φ.1 : J → Q))
    (fun _ _ hφ => Subtype.ext (DFunLike.coe_injective hφ))
  let R := Set.range fun φ : GroupEpimorphism J Q => h.top.comp φ.1
  letI : Finite R := Set.finite_range _ |>.to_subtype
  let D := ⌊d⌋₊
  have hfibre : ∀ θ : R, Nat.card {φ : GroupEpimorphism J Q //
      (⟨h.top.comp φ.1, φ, rfl⟩ : R) = θ} ≤ Nat.card Q * 2 ^ (h.weight * D) := by
    intro θ
    obtain ⟨φ₀, hφ₀⟩ := θ.2
    have hθ : Function.Surjective θ.1 := by
      rw [← hφ₀]
      exact h.top_surjective.comp φ₀.2
    have hdθ : binaryCharacterRank θ.1.ker ≤ D :=
      Nat.le_floor (hd θ.1 hθ)
    refine le_trans ?_ ((h.fibre_card_le θ.1 hθ).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num)
        (Nat.mul_le_mul_left _ hdθ))))
    apply Nat.card_le_card_of_injective
      (fun φ => (⟨φ.1, congrArg Subtype.val φ.2⟩ :
        {φ : GroupEpimorphism J Q // h.top.comp φ.1 = θ.1}))
    intro φ φ' hφ
    simp only [Subtype.mk.injEq] at hφ
    exact Subtype.ext hφ
  have hnat := natCard_le_mul_of_fibre
    (fun φ : GroupEpimorphism J Q => (⟨h.top.comp φ.1, φ, rfl⟩ : R)) _ hfibre
  have hR := h.realisedTops_card_le (J := J)
  rcases Nat.eq_zero_or_pos (Nat.card R) with h0 | hpos
  · have : Nat.card (GroupEpimorphism J Q) = 0 := by
      have := hnat
      rw [h0, zero_mul] at this
      omega
    rw [this, Nat.cast_zero]
    positivity
  · obtain ⟨θ⟩ := (Nat.card_pos_iff.mp hpos).1
    obtain ⟨φ₀, hφ₀⟩ := θ.2
    have hθ : Function.Surjective θ.1 := by
      rw [← hφ₀]
      exact h.top_surjective.comp φ₀.2
    have hd0 : 0 ≤ d := (Nat.cast_nonneg _).trans (hd θ.1 hθ)
    have hD : (D : ℝ) ≤ d := Nat.floor_le hd0
    have hcast : (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
        (binaryCharacterRank (commutator J) : ℝ) * Nat.card Q *
          (2 : ℝ) ^ ((h.weight * D : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      have := hnat.trans (Nat.mul_le_mul_right _ hR)
      calc (Nat.card (GroupEpimorphism J Q) : ℝ)
          ≤ ((binaryCharacterRank (commutator J) *
              (Nat.card Q * 2 ^ (h.weight * D)) : ℕ) : ℝ) := by
            exact_mod_cast this
        _ = _ := by push_cast; ring
    refine hcast.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    exact mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg _)

end ScalarFourHeadedQuotient

end SymmetricSubgroupAsymptotics
