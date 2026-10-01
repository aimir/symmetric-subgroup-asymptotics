import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelRelabel
import SymmetricSubgroupAsymptotics.PermutationPrimeGroupRank
import SymmetricSubgroupAsymptotics.Non2PreE7DerivedHeadBounds
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Primitive affine groups `V ⋊ R`

For a prime `p`, `V = F_p^d` and a subgroup `R ≤ GL(V)` acting irreducibly,
the affine group `U = V ⋊ R` acts on `V` by `x ↦ r x + v`.  The translation
subgroup is a self-centralizing minimal normal subgroup and `U / V ≅ R`, so
every nontrivial normal subgroup contains `V`.  If `R` is soluble and
nontrivial of derived length `t + 1`, then `U^(t+1) = V`, and `U` is a
cyclic-dual target over `F_p` on the common source `J^(t+1)`:

`|Epi(J, U)| ≤ |Aut U| · p^(d_p(J^(t+1))) ≤ |Aut U| · 2^((log₂ p / p) b)`.
-/

set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics
namespace DerivedHead
namespace DerivedCyclicTarget

variable {Q : Type*} [Group Q] [Finite Q] {V : Subgroup Q} [V.Normal] {n : ℕ}

/-- Cyclic-dual targets over any prime:
`|Epi(J, Q)| ≤ |Aut Q| · 2^((log₂ p / p) b)`. -/
theorem epi_card_le_prime {p : ℕ} [Fact p.Prime] (D : DerivedCyclicTarget Q V n p) {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      (Nat.card (Q ≃* Q) : ℝ) * (2 : ℝ) ^ ((Real.logb 2 p / p) * b) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have h := D.epi_card_le (J := J)
  rw [card_hom_zmod_eq p] at h
  have hr := primeRank_le_of_subgroup p J (derivedSeries J (n + 1))
  have hpow : (p : ℝ) ^ Module.finrank (ZMod p) (PrimeCharacters p (derivedSeries J (n + 1)))
      ≤ (2 : ℝ) ^ ((Real.logb 2 p / p) * b) := by
    calc (p : ℝ) ^ Module.finrank (ZMod p) (PrimeCharacters p (derivedSeries J (n + 1)))
        ≤ (p : ℝ) ^ (b / p) := pow_le_pow_right₀ (by exact_mod_cast hp1) hr
      _ ≤ (2 : ℝ) ^ ((Real.logb 2 p / p) * b) := pow_floor_div_le_rpow p b hp1
  calc (Nat.card (GroupEpimorphism J Q) : ℝ)
      ≤ ((p ^ Module.finrank (ZMod p) (PrimeCharacters p (derivedSeries J (n + 1))) *
          Nat.card (Q ≃* Q) : ℕ) : ℝ) := by exact_mod_cast h
    _ = (Nat.card (Q ≃* Q) : ℝ) *
          (p : ℝ) ^ Module.finrank (ZMod p) (PrimeCharacters p (derivedSeries J (n + 1))) := by
        push_cast
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)

end DerivedCyclicTarget
end DerivedHead

namespace AffineModel

open Equiv SemidirectProduct

variable {p d : ℕ} [hp : Fact p.Prime]

/-- `V = F_p^d`. -/
abbrev V (p d : ℕ) := Fin d → ZMod p

/-- `GL(V)`. -/
abbrev GLV (p d : ℕ) := V p d ≃ₗ[ZMod p] V p d

variable (R : Subgroup (GLV p d))

/-- The linear action on the multiplicative translations. -/
def linAut : R →* MulAut (Multiplicative (V p d)) where
  toFun r := ((r : GLV p d).toAddEquiv).toMultiplicative
  map_one' := by
    ext v
    rfl
  map_mul' r s := by
    ext v
    rfl

/-- The affine group `V ⋊ R`. -/
abbrev Aff := Multiplicative (V p d) ⋊[linAut R] R

instance : NeZero p := ⟨hp.out.ne_zero⟩

instance finiteGLV : Finite (GLV p d) :=
  Finite.of_injective (fun f : GLV p d => (f : V p d → V p d)) DFunLike.coe_injective

instance : Finite (Aff R) := Finite.of_equiv _ SemidirectProduct.equivProd.symm

theorem linAut_apply (r : R) (v : Multiplicative (V p d)) :
    linAut R r v = Multiplicative.ofAdd ((r : GLV p d) (Multiplicative.toAdd v)) := rfl

/-- Translations. -/
def transl : Multiplicative (V p d) →* Perm (V p d) where
  toFun v := Equiv.addLeft (Multiplicative.toAdd v)
  map_one' := by
    ext x
    simp
  map_mul' v w := by
    ext x
    simp

/-- Linear maps. -/
def linPerm : R →* Perm (V p d) where
  toFun r := (r : GLV p d).toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The natural affine action on `V`. -/
def action : Aff R →* Perm (V p d) :=
  SemidirectProduct.lift transl (linPerm R) (by
    intro r
    refine MonoidHom.ext fun v => Equiv.ext fun x => ?_
    change Multiplicative.toAdd (linAut R r v) + x =
      (r : GLV p d) (Multiplicative.toAdd v + (r : GLV p d).symm x)
    rw [map_add, LinearEquiv.apply_symm_apply]
    rfl)

theorem action_apply (y : Aff R) (x : V p d) :
    action R y x = Multiplicative.toAdd y.left + (y.right : GLV p d) x := rfl

theorem action_injective : Function.Injective (action R) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have h : ∀ x, Multiplicative.toAdd y.left + (y.right : GLV p d) x = x := by
    intro x
    rw [← action_apply, hy]
    rfl
  have hv : y.left = 1 := by
    have := h 0
    rw [map_zero, add_zero] at this
    exact Multiplicative.toAdd.injective this
  have hr : y.right = 1 := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    have := h x
    rw [hv, toAdd_one, zero_add] at this
    exact this
  exact SemidirectProduct.ext hv hr

/-! ## The translation subgroup -/

/-- The translation subgroup. -/
def Vsub : Subgroup (Aff R) := (inl : Multiplicative (V p d) →* Aff R).range

instance : (Vsub R).Normal := by
  rw [Vsub, range_inl_eq_ker_rightHom]
  exact MonoidHom.normal_ker _

theorem mem_Vsub (y : Aff R) : y ∈ Vsub R ↔ y.right = 1 := by
  rw [Vsub, range_inl_eq_ker_rightHom, MonoidHom.mem_ker, rightHom_eq_right]

theorem conj_inl (y : Aff R) (w : Multiplicative (V p d)) :
    y * inl w * y⁻¹ = inl (linAut R y.right w) := by
  conv_lhs => rw [← inl_left_mul_inr_right y]
  have h1 : (inr y.right : Aff R) * inl w * (inr y.right)⁻¹ = inl (linAut R y.right w) := by
    rw [← map_inv]
    exact (inl_aut _ _).symm
  calc (inl y.left * inr y.right : Aff R) * inl w * (inl y.left * inr y.right)⁻¹
      = (inl y.left : Aff R) * ((inr y.right : Aff R) * inl w * (inr y.right)⁻¹) *
          (inl y.left)⁻¹ := by group
    _ = (inl (y.left * linAut R y.right w * y.left⁻¹) : Aff R) := by
        rw [h1, ← map_inv, ← map_mul, ← map_mul]
    _ = _ := by rw [mul_comm y.left, mul_inv_cancel_right]

theorem selfCentralizing (y : Aff R) (hy : ∀ v ∈ Vsub R, y * v = v * y) : y ∈ Vsub R := by
  rw [mem_Vsub]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have h := hy (inl (Multiplicative.ofAdd x)) ⟨_, rfl⟩
  have h2 : y * inl (Multiplicative.ofAdd x) * y⁻¹ = inl (Multiplicative.ofAdd x) := by
    rw [h, mul_inv_cancel_right]
  rw [conj_inl] at h2
  have := congrArg Multiplicative.toAdd (inl_injective h2)
  exact this

/-- Irreducibility of `R`. -/
def Irreducible : Prop :=
  ∀ S : AddSubgroup (V p d), (∀ r ∈ R, ∀ x ∈ S, (r : GLV p d) x ∈ S) → S = ⊥ ∨ S = ⊤

variable {R}

theorem minimal (hirr : Irreducible R) (W : Subgroup (Aff R)) (hW : W.Normal)
    (hWV : W ≤ Vsub R) : W = ⊥ ∨ W = Vsub R := by
  let S : AddSubgroup (V p d) :=
    { carrier := {x | inl (Multiplicative.ofAdd x) ∈ W}
      zero_mem' := by
        show inl (Multiplicative.ofAdd (0 : V p d)) ∈ W
        rw [ofAdd_zero, map_one]
        exact W.one_mem
      add_mem' := by
        intro a b ha hb
        show inl (Multiplicative.ofAdd (a + b)) ∈ W
        rw [ofAdd_add, map_mul]
        exact W.mul_mem ha hb
      neg_mem' := by
        intro a ha
        show inl (Multiplicative.ofAdd (-a)) ∈ W
        rw [ofAdd_neg, map_inv]
        exact W.inv_mem ha }
  have hinv : ∀ r ∈ R, ∀ x ∈ S, (r : GLV p d) x ∈ S := by
    intro r hr x hx
    have := hW.conj_mem _ hx (inr ⟨r, hr⟩)
    rw [conj_inl] at this
    exact this
  rcases hirr S hinv with h | h
  · left
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨v, rfl⟩ := hWV hy
    have : Multiplicative.toAdd v ∈ S := by
      show inl (Multiplicative.ofAdd (Multiplicative.toAdd v)) ∈ W
      exact hy
    rw [h] at this
    have hv : v = 1 := Multiplicative.toAdd.injective ((AddSubgroup.mem_bot).mp this)
    rw [hv, map_one]
    exact Subgroup.one_mem _
  · right
    apply le_antisymm hWV
    rintro _ ⟨v, rfl⟩
    have : Multiplicative.toAdd v ∈ S := by
      rw [h]
      exact AddSubgroup.mem_top _
    exact this

/-- In a faithful irreducible affine group, every nontrivial normal subgroup
contains the translation subgroup.  This is the literal normal-menu fact
used by all soluble primitive affine owners. -/
theorem Vsub_le_normal (hirr : Irreducible R) (N : Subgroup (Aff R))
    [hN : N.Normal] (hNb : N ≠ ⊥) : Vsub R ≤ N :=
  le_of_minimal_selfCentralizing (Vsub R) (minimal hirr)
    (selfCentralizing R) N hNb

/-! ## The derived series -/

/-- A nontrivial element of the linear part moves some vector, so it has a
nontrivial commutator with the translations. -/
theorem comm_ne_bot (H : Subgroup (Aff R)) (r : R) (hr : r ≠ 1)
    (hH : ∃ y ∈ H, y.right = r) : ⁅H, Vsub R⁆ ≠ ⊥ := by
  obtain ⟨y, hyH, hyr⟩ := hH
  have hmove : ∃ x : V p d, (r : GLV p d) x ≠ x := by
    by_contra hall
    push Not at hall
    exact hr (Subtype.ext (LinearEquiv.ext hall))
  obtain ⟨x, hx⟩ := hmove
  intro hbot
  have hmem : ⁅y, inl (Multiplicative.ofAdd x)⁆ ∈ ⁅H, Vsub R⁆ :=
    Subgroup.commutator_mem_commutator hyH ⟨_, rfl⟩
  rw [hbot] at hmem
  have h1 : ⁅y, inl (Multiplicative.ofAdd x)⁆ = 1 := (Subgroup.mem_bot).mp hmem
  rw [commutatorElement_def, conj_inl, hyr, ← map_inv, ← map_mul] at h1
  apply hx
  have := congrArg Multiplicative.toAdd (inl_injective (h1.trans (map_one _).symm))
  simp only [linAut_apply, toAdd_mul, toAdd_ofAdd, toAdd_inv, toAdd_one] at this
  exact sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact this)

variable (R)

/-- The derived length data of a nontrivial soluble `R`. -/
structure DerivedLength where
  t : ℕ
  top_eq : derivedSeries R (t + 1) = ⊥
  prev_ne : derivedSeries R t ≠ ⊥

omit hp in
theorem derivedLength_nonempty [hsol : IsSolvable R] (hR : R ≠ ⊥) :
    Nonempty (DerivedLength R) := by
  classical
  have hex : ∃ n, derivedSeries R n = ⊥ := (isSolvable_def R).mp hsol
  let n := Nat.find hex
  have hn : derivedSeries R n = ⊥ := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro h0
    have : derivedSeries R 0 = ⊥ := h0 ▸ hn
    rw [derivedSeries_zero] at this
    apply hR
    rw [eq_bot_iff]
    intro r _
    have hr : (⟨r, ‹_›⟩ : R) ∈ (⊤ : Subgroup R) := Subgroup.mem_top _
    rw [this] at hr
    exact congrArg Subtype.val ((Subgroup.mem_bot).mp hr)
  refine ⟨⟨n - 1, ?_, ?_⟩⟩
  · rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0)]
    exact hn
  · exact Nat.find_min hex (by omega)

variable {R}

omit hp in
theorem exists_ne_one (L : DerivedLength R) : ∃ r : R, r ∈ derivedSeries R L.t ∧ r ≠ 1 := by
  obtain ⟨⟨r, hrt⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp L.prev_ne
  exact ⟨r, hrt, fun h => hr1 (Subtype.ext h)⟩

theorem comm_derived_ne_bot (L : DerivedLength R) (k : ℕ) (hk : k ≤ L.t) :
    ⁅derivedSeries (Aff R) k, Vsub R⁆ ≠ ⊥ := by
  obtain ⟨r, hrt, hr1⟩ := exists_ne_one L
  have hrk : r ∈ derivedSeries R k := derivedSeries_antitone R hk hrt
  rw [← map_derivedSeries_eq (rightHom_surjective : Function.Surjective
    (rightHom : Aff R →* R)) k] at hrk
  obtain ⟨y, hy, hyr⟩ := hrk
  exact comm_ne_bot _ r hr1 ⟨y, hy, hyr⟩

theorem derived_eq (hirr : Irreducible R) (L : DerivedLength R) :
    derivedSeries (Aff R) (L.t + 1) = Vsub R := by
  apply le_antisymm
  · intro y hy
    have h := map_derivedSeries_le_derivedSeries (rightHom : Aff R →* R) (L.t + 1) ⟨y, hy, rfl⟩
    rw [L.top_eq] at h
    rw [mem_Vsub]
    exact (Subgroup.mem_bot).mp h
  · have hk : ∀ k, k ≤ L.t + 1 → Vsub R ≤ derivedSeries (Aff R) k := by
      intro k
      induction k with
      | zero =>
        intro _
        rw [derivedSeries_zero]
        exact le_top
      | succ k ih =>
        intro hkt
        have hprev := ih (by omega)
        have hne := comm_derived_ne_bot L k (by omega)
        have hnorm : (⁅derivedSeries (Aff R) k, Vsub R⁆).Normal :=
          Subgroup.commutator_normal _ _
        rcases minimal hirr _ hnorm (Subgroup.commutator_le_right _ _) with h | h
        · exact absurd h hne
        · rw [← h, derivedSeries_succ]
          exact Subgroup.commutator_mono le_rfl hprev
    exact hk (L.t + 1) le_rfl

/-! ## The cyclic-dual target -/

/-- A nonzero coordinate character of the translations. -/
def coordChar (hd : 0 < d) : Vsub R →* Multiplicative (ZMod p) where
  toFun y := Multiplicative.ofAdd (Multiplicative.toAdd (y : Aff R).left ⟨0, hd⟩)
  map_one' := rfl
  map_mul' y z := by
    have hy : (y : Aff R).right = 1 := (mem_Vsub R _).mp y.2
    show Multiplicative.ofAdd (Multiplicative.toAdd ((y : Aff R) * z).left ⟨0, hd⟩) = _
    rw [mul_left, hy, map_one]
    rfl

theorem coordChar_ne_one (hd : 0 < d) : coordChar (R := R) hd ≠ 1 := by
  intro h
  let e : V p d := Pi.single (M := fun _ : Fin d => ZMod p) ⟨0, hd⟩ 1
  have := DFunLike.congr_fun h ⟨inl (Multiplicative.ofAdd e), ⟨_, rfl⟩⟩
  change Multiplicative.ofAdd (e ⟨0, hd⟩) = 1 at this
  rw [show e ⟨0, hd⟩ = 1 from Pi.single_eq_same _ _] at this
  exact one_ne_zero (Multiplicative.ofAdd.injective this)

/-- The affine group is a cyclic-dual target over `F_p`. -/
def target (hirr : Irreducible R) (L : DerivedLength R) (hd : 0 < d) :
    DerivedHead.DerivedCyclicTarget (Aff R) (Vsub R) L.t p where
  derived_eq := derived_eq hirr L
  character := coordChar hd
  self_centralizing := selfCentralizing R
  absorbing := by
    intro W hW hWV
    rcases minimal hirr W hW hWV with h | h
    · rw [h]
      exact bot_le
    · have hne := comm_derived_ne_bot L L.t le_rfl
      have hnorm : (⁅derivedSeries (Aff R) L.t, Vsub R⁆).Normal :=
        Subgroup.commutator_normal _ _
      rcases minimal hirr _ hnorm (Subgroup.commutator_le_right _ _) with h' | h'
      · exact absurd h' hne
      · rw [h]
        exact h'.symm.le
  separating := DerivedHead.separating_of_minimal (minimal hirr) _ (coordChar_ne_one hd)

end AffineModel
end SymmetricSubgroupAsymptotics
