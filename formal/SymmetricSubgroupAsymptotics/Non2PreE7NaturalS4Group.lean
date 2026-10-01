import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelToolkit

/-!
# The literal normal menu and second derived head of natural `S₄`

The Klein subgroup `V₄` of `S₄ = Perm (Fin 4)` is the kernel of the action on
the three pairings, a surjection onto `S₃`.  It is minimal normal and
self-centralizing, so every nontrivial normal subgroup of `S₄` contains it,
and it is the second derived subgroup.  One character of `V₄` has a
stabilizer fixing only two characters.  These are the inputs of the
common-head count at `m = 2`, `q = 2`.

All finite facts are checked by `decide` on the literal permutations.
-/

set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics
namespace NaturalS4

open Equiv

/-- The three involutions of the Klein subgroup. -/
def c1 : Perm (Fin 4) := swap 0 1 * swap 2 3
def c2 : Perm (Fin 4) := swap 0 2 * swap 1 3
def c3 : Perm (Fin 4) := swap 0 3 * swap 1 2

/-- The literal elements of `V₄`. -/
def kleinSet : Finset (Perm (Fin 4)) := {1, c1, c2, c3}

theorem kleinSet_mul : ∀ a b : Perm (Fin 4), a ∈ kleinSet → b ∈ kleinSet →
    a * b ∈ kleinSet := by decide

theorem kleinSet_inv : ∀ a : Perm (Fin 4), a ∈ kleinSet → a⁻¹ ∈ kleinSet := by decide

/-- The Klein subgroup. -/
def klein : Subgroup (Perm (Fin 4)) where
  carrier := {σ | σ ∈ kleinSet}
  mul_mem' ha hb := kleinSet_mul _ _ ha hb
  one_mem' := by decide
  inv_mem' ha := kleinSet_inv _ ha

theorem mem_klein (σ : Perm (Fin 4)) : σ ∈ klein ↔ σ ∈ kleinSet := Iff.rfl

instance : DecidablePred (· ∈ klein) := fun σ => inferInstanceAs (Decidable (σ ∈ kleinSet))

/-- The index of the pairing containing `{a, b}`. -/
def pairOf (a b : Fin 4) : Fin 3 :=
  if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) then 0
  else if (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨ (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1) then 1
  else 2

/-- The action of a permutation on the three pairings. -/
def pairFun (σ : Perm (Fin 4)) (i : Fin 3) : Fin 3 := pairOf (σ 0) (σ i.succ)

theorem pairFun_mul : ∀ σ τ : Perm (Fin 4), ∀ i : Fin 3,
    pairFun (σ * τ) i = pairFun σ (pairFun τ i) := by decide

theorem pairFun_one : ∀ i : Fin 3, pairFun 1 i = i := by decide

/-- The permutation of the pairings. -/
def pairPerm (σ : Perm (Fin 4)) : Perm (Fin 3) where
  toFun := pairFun σ
  invFun := pairFun σ⁻¹
  left_inv i := by
    rw [← pairFun_mul, inv_mul_cancel, pairFun_one]
  right_inv i := by
    rw [← pairFun_mul, mul_inv_cancel, pairFun_one]

/-- The surjection `S₄ → S₃` onto the pairing action. -/
def pairing : Perm (Fin 4) →* Perm (Fin 3) where
  toFun := pairPerm
  map_one' := by
    ext i
    exact congrArg Fin.val (pairFun_one i)
  map_mul' σ τ := by
    ext i
    exact congrArg Fin.val (pairFun_mul σ τ i)

theorem pairing_apply (σ : Perm (Fin 4)) (i : Fin 3) : pairing σ i = pairFun σ i := rfl

theorem pairing_eq_one_iff : ∀ σ : Perm (Fin 4), (∀ i : Fin 3, pairFun σ i = i) ↔
    σ ∈ kleinSet := by decide

theorem ker_pairing : pairing.ker = klein := by
  ext σ
  rw [MonoidHom.mem_ker, mem_klein, ← pairing_eq_one_iff]
  constructor
  · intro h i
    have := congrArg (fun τ : Perm (Fin 3) => τ i) h
    simpa [pairing_apply] using this
  · intro h
    ext i
    simp [pairing_apply, h i]

theorem pairFun_surjective : ∀ τ : Perm (Fin 3), ∃ σ : Perm (Fin 4),
    ∀ i : Fin 3, pairFun σ i = τ i := by decide

theorem pairing_surjective : Function.Surjective pairing := by
  intro τ
  obtain ⟨σ, hσ⟩ := pairFun_surjective τ
  exact ⟨σ, by ext i; simp [pairing_apply, hσ i]⟩

/-! ## Normality, centralizer and minimality -/

theorem kleinSet_conj : ∀ g v : Perm (Fin 4), v ∈ kleinSet → g * v * g⁻¹ ∈ kleinSet := by
  decide

instance klein_normal : klein.Normal := ⟨fun v hv g => kleinSet_conj g v hv⟩

theorem kleinSet_cases {v : Perm (Fin 4)} (hv : v ∈ kleinSet) :
    v = 1 ∨ v = c1 ∨ v = c2 ∨ v = c3 := by
  simpa [kleinSet] using hv

theorem centralizer_kleinSet : ∀ x : Perm (Fin 4), x * c1 = c1 * x → x * c2 = c2 * x →
    x * c3 = c3 * x → x ∈ kleinSet := by decide

theorem klein_selfCentralizing (x : Perm (Fin 4)) (hx : ∀ v ∈ klein, x * v = v * x) :
    x ∈ klein :=
  centralizer_kleinSet x (hx c1 (by decide)) (hx c2 (by decide)) (hx c3 (by decide))

theorem kleinSet_conjugates : ∀ v ∈ kleinSet, v ≠ 1 → ∀ w ∈ kleinSet,
    w = 1 ∨ ∃ g : Perm (Fin 4), g * v * g⁻¹ = w := by decide

theorem klein_minimal (W : Subgroup (Perm (Fin 4))) (hW : W.Normal) (hWV : W ≤ klein) :
    W = ⊥ ∨ W = klein := by
  by_cases hb : W = ⊥
  · exact Or.inl hb
  right
  obtain ⟨⟨v, hvW⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hb
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  apply le_antisymm hWV
  intro w hw
  rcases kleinSet_conjugates v (hWV hvW) hv1' w hw with h | ⟨g, hg⟩
  · rw [h]
    exact W.one_mem
  · rw [← hg]
    exact hW.conj_mem v hvW g

theorem kleinSet_comm : ∀ v ∈ kleinSet, ∀ w ∈ kleinSet, v * w = w * v := by decide

theorem kleinSet_sq : ∀ v ∈ kleinSet, v ^ 2 = 1 := by decide

theorem card_klein : Nat.card klein = 2 ^ 2 := by
  rw [show Nat.card klein = Nat.card {σ // σ ∈ kleinSet} from rfl, Nat.card_eq_finsetCard]
  decide

/-! ## The derived series -/

theorem mem_derivedSeries_succ {G : Type*} [Group G] {n : ℕ} {x y : G}
    (hx : x ∈ derivedSeries G n) (hy : y ∈ derivedSeries G n) :
    ⁅x, y⁆ ∈ derivedSeries G (n + 1) := by
  rw [derivedSeries_succ]
  exact Subgroup.commutator_mem_commutator hx hy

theorem mem_derivedSeries_one {G : Type*} [Group G] (x y : G) :
    ⁅x, y⁆ ∈ derivedSeries G 1 :=
  mem_derivedSeries_succ (by simp [derivedSeries_zero]) (by simp [derivedSeries_zero])

/-- The 3-cycle used as a fixed-point-free element of the first derived term. -/
def t3 : Perm (Fin 4) := ⁅(swap 0 1 : Perm (Fin 4)), swap 0 2⁆

theorem t3_mem : t3 ∈ derivedSeries (Perm (Fin 4)) 1 := mem_derivedSeries_one _ _

theorem c1_eq : c1 = ⁅t3, ⁅(swap 0 1 : Perm (Fin 4)), swap 0 3⁆⁆ := by decide
theorem c2_eq : c2 = ⁅t3, ⁅(swap 0 2 : Perm (Fin 4)), swap 2 3⁆⁆ := by decide
theorem c3_eq : c3 = ⁅t3, ⁅(swap 0 1 : Perm (Fin 4)), swap 1 3⁆⁆ := by decide

/-- The alternating group of degree three, as literal elements. -/
def a3Set : Finset (Perm (Fin 3)) := {1, swap 0 1 * swap 1 2, swap 1 2 * swap 0 1}

theorem a3Set_mul : ∀ a b : Perm (Fin 3), a ∈ a3Set → b ∈ a3Set → a * b ∈ a3Set := by
  decide

theorem a3Set_inv : ∀ a : Perm (Fin 3), a ∈ a3Set → a⁻¹ ∈ a3Set := by decide

def a3 : Subgroup (Perm (Fin 3)) where
  carrier := {σ | σ ∈ a3Set}
  mul_mem' ha hb := a3Set_mul _ _ ha hb
  one_mem' := by decide
  inv_mem' ha := a3Set_inv _ ha

theorem commutator_mem_a3Set : ∀ a b : Perm (Fin 3), ⁅a, b⁆ ∈ a3Set := by decide

theorem a3Set_commute : ∀ a ∈ a3Set, ∀ b ∈ a3Set, ⁅a, b⁆ = (1 : Perm (Fin 3)) := by decide

theorem derivedSeries_S3_two : derivedSeries (Perm (Fin 3)) 2 = ⊥ := by
  have h1 : derivedSeries (Perm (Fin 3)) 1 ≤ a3 := by
    rw [derivedSeries_succ, derivedSeries_zero, Subgroup.commutator_le]
    intro a _ b _
    exact commutator_mem_a3Set a b
  rw [eq_bot_iff, derivedSeries_succ]
  calc ⁅derivedSeries (Perm (Fin 3)) 1, derivedSeries (Perm (Fin 3)) 1⁆ ≤ ⁅a3, a3⁆ :=
        Subgroup.commutator_mono h1 h1
    _ ≤ ⊥ := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        rw [a3Set_commute a ha b hb]
        exact Subgroup.one_mem _

theorem derivedSeries_two : derivedSeries (Perm (Fin 4)) 2 = klein := by
  apply le_antisymm
  · intro x hx
    have hmap := map_derivedSeries_le_derivedSeries pairing 2 ⟨x, hx, rfl⟩
    rw [derivedSeries_S3_two] at hmap
    rw [← ker_pairing]
    exact (Subgroup.mem_bot).mp hmap
  · intro v hv
    rcases kleinSet_cases hv with h | h | h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h, c1_eq]
      exact mem_derivedSeries_succ t3_mem (mem_derivedSeries_one _ _)
    · rw [h, c2_eq]
      exact mem_derivedSeries_succ t3_mem (mem_derivedSeries_one _ _)
    · rw [h, c3_eq]
      exact mem_derivedSeries_succ t3_mem (mem_derivedSeries_one _ _)

theorem t3_fixedPointFree : ∀ v ∈ kleinSet, t3 * v * t3⁻¹ = v → v = 1 := by decide

theorem klein_absorbing (W : Subgroup (Perm (Fin 4))) (hW : W.Normal) (hWV : W ≤ klein) :
    W ≤ ⁅derivedSeries (Perm (Fin 4)) 1, W⁆ := by
  apply DerivedHead.absorbing_of_fixedPointFree 1 t3 t3_mem
  · rw [derivedSeries_two]
    exact kleinSet_comm
  · rw [derivedSeries_two]
    exact t3_fixedPointFree
  · exact hW
  · rw [derivedSeries_two]
    exact hWV

/-! ## The character witness -/

/-- The indicator of the two involutions off the first pairing. -/
def offFirst (σ : Perm (Fin 4)) : ZMod 2 := if σ = c2 ∨ σ = c3 then 1 else 0

theorem offFirst_mul : ∀ a ∈ kleinSet, ∀ b ∈ kleinSet,
    offFirst (a * b) = offFirst a + offFirst b := by decide

/-- The character of `V₄` with kernel `{1, c1}`. -/
def chi0 : PrimeCharacters 2 klein where
  toFun a := offFirst ((Additive.toMul a : klein) : Perm (Fin 4))
  map_zero' := by decide
  map_add' a b := offFirst_mul _ (Additive.toMul a).2 _ (Additive.toMul b).2

def k1 : klein := ⟨c1, by decide⟩
def k2 : klein := ⟨c2, by decide⟩
def k3 : klein := ⟨c3, by decide⟩

theorem klein_cases (v : klein) : v = 1 ∨ v = k1 ∨ v = k2 ∨ v = k3 := by
  rcases kleinSet_cases v.2 with h | h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))

theorem k1_eq : k1 = k2 * k3 := Subtype.ext (by decide)

theorem chi_k1 (χ : PrimeCharacters 2 klein) :
    χ (Additive.ofMul k1) = χ (Additive.ofMul k2) + χ (Additive.ofMul k3) := by
  rw [k1_eq, ofMul_mul, map_add]

theorem swap_conj_k2 : MulAut.conjNormal (swap (0 : Fin 4) 1)⁻¹ k2 = k3 := by
  apply Subtype.ext
  simp only [MulAut.conjNormal_apply, inv_inv]
  decide

theorem offFirst_swap : ∀ v ∈ kleinSet,
    offFirst ((swap (0 : Fin 4) 1)⁻¹ * v * (swap (0 : Fin 4) 1)⁻¹⁻¹) = offFirst v := by decide

theorem chi0_fixed : DerivedHead.conjRep 2 (Perm (Fin 4)) klein (swap 0 1) chi0 = chi0 := by
  refine AddMonoidHom.ext fun v' => ?_
  change DerivedHead.conjRep 2 (Perm (Fin 4)) klein (swap 0 1) chi0
      (Additive.ofMul (Additive.toMul v')) = chi0 (Additive.ofMul (Additive.toMul v'))
  generalize Additive.toMul v' = v
  rw [DerivedHead.conjRep_apply]
  show offFirst ((MulAut.conjNormal (swap (0 : Fin 4) 1)⁻¹ v : klein) : Perm (Fin 4)) =
    offFirst (v : Perm (Fin 4))
  simp only [MulAut.conjNormal_apply]
  exact offFirst_swap _ v.2

theorem chi0_ne_zero : chi0 ≠ 0 := by
  intro h
  have := DFunLike.congr_fun h (Additive.ofMul k2)
  revert this
  decide

/-- The characters fixed by the stabilizer of `chi0` number at most two. -/
theorem chi0_stabilizer_card :
    Nat.card {χ : PrimeCharacters 2 klein //
      ∀ x : Perm (Fin 4), DerivedHead.conjRep 2 (Perm (Fin 4)) klein x chi0 = chi0 →
        DerivedHead.conjRep 2 (Perm (Fin 4)) klein x χ = χ} ≤ 2 := by
  let ev : {χ : PrimeCharacters 2 klein //
      ∀ x : Perm (Fin 4), DerivedHead.conjRep 2 (Perm (Fin 4)) klein x chi0 = chi0 →
        DerivedHead.conjRep 2 (Perm (Fin 4)) klein x χ = χ} → ZMod 2 :=
    fun χ => χ.1 (Additive.ofMul k2)
  have key : ∀ χ : {χ : PrimeCharacters 2 klein //
      ∀ x : Perm (Fin 4), DerivedHead.conjRep 2 (Perm (Fin 4)) klein x chi0 = chi0 →
        DerivedHead.conjRep 2 (Perm (Fin 4)) klein x χ = χ},
      χ.1 (Additive.ofMul k3) = χ.1 (Additive.ofMul k2) ∧ χ.1 (Additive.ofMul k1) = 0 := by
    intro χ
    have hfix := χ.2 (swap 0 1) chi0_fixed
    have h3 : χ.1 (Additive.ofMul k3) = χ.1 (Additive.ofMul k2) := by
      have := DFunLike.congr_fun hfix (Additive.ofMul k2)
      rw [DerivedHead.conjRep_apply, swap_conj_k2] at this
      exact this
    refine ⟨h3, ?_⟩
    rw [chi_k1, h3]
    generalize χ.1 (Additive.ofMul k2) = a
    revert a
    decide
  have hev : Function.Injective ev := by
    intro χ χ' h
    apply Subtype.ext
    refine AddMonoidHom.ext fun v' => ?_
    change χ.1 (Additive.ofMul (Additive.toMul v')) = χ'.1 (Additive.ofMul (Additive.toMul v'))
    generalize Additive.toMul v' = v
    obtain ⟨h3, h1⟩ := key χ
    obtain ⟨h3', h1'⟩ := key χ'
    have h2 : χ.1 (Additive.ofMul k2) = χ'.1 (Additive.ofMul k2) := h
    rcases klein_cases v with hv | hv | hv | hv <;> rw [hv]
    · rw [ofMul_one, map_zero, map_zero]
    · rw [h1, h1']
    · exact h2
    · rw [h3, h3', h2]
  calc Nat.card _ ≤ Nat.card (ZMod 2) := Nat.card_le_card_of_injective ev hev
    _ = 2 := Nat.card_zmod 2

/-! ## The common-head target -/

/-- Natural `S₄` is a common-head target with source `J''`, `m = 2`, `q = 2`. -/
theorem derivedHeadTarget : DerivedHead.DerivedHeadTarget 2 (Perm (Fin 4)) klein 1 2 2 where
  derived_eq := derivedSeries_two
  self_centralizing := klein_selfCentralizing
  absorbing := klein_absorbing
  commutative := kleinSet_comm
  exponent := kleinSet_sq
  minimal := klein_minimal
  finrank_eq := DerivedHead.finrank_characters_eq 2 klein kleinSet_comm kleinSet_sq 2 card_klein
  witness := ⟨chi0, chi0_ne_zero, chi0_stabilizer_card⟩

/-- `|Epi(J, S₄)| ≤ 2 |Aut S₄| · 2^(b/4)` on every actual source. -/
theorem epi_card_le {b : ℕ} (J : Subgroup (Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (Perm (Fin 4))) : ℝ) ≤
      (2 * Nat.card (Perm (Fin 4) ≃* Perm (Fin 4)) : ℝ) * (2 : ℝ) ^ ((1 / 4 : ℝ) * b) := by
  have h := DerivedHead.DerivedHeadTarget.epi_card_le_binary derivedHeadTarget le_rfl J
  convert h using 3
  have hl : Real.logb 2 ((2 : ℕ) : ℝ) = 1 := by
    rw [Nat.cast_ofNat, Real.logb_self_eq_one (by norm_num)]
  rw [hl]
  norm_num

end NaturalS4
end SymmetricSubgroupAsymptotics
