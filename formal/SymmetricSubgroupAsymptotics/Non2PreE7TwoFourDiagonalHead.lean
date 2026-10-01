import SymmetricSubgroupAsymptotics.Non2PreE7TwoFourDiagonalMenu
import SymmetricSubgroupAsymptotics.Non2PreE7DerivedHeadBounds

/-!
# Common derived sources and normal menus of the TF classes

For each named class `X ∈ {Xc, Xg, Xs}` the base `V = V₄ × V₄` is a
self-centralizing normal subgroup.  It is the derived subgroup of `Xc` and
the second derived subgroup of `Xg` and `Xs`; the diagonal three-cycle `a`
lies in the previous derived term and acts on `V` without fixed points.
The first-coordinate character of `V`, together with its conjugates under
`a` and a block exchange of `X`, separates `V`.  Hence each class is a
binary cyclic-dual target, and `|Epi(J, X)| ≤ |Aut X| · 2^(b/2)`.
-/

set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics
namespace TwoFourDiagonal

open Equiv NaturalS4 C2Wreath SemidirectProduct

theorem tLoc_eq_t3 : tLoc = t3 := by decide

/-! ## Conjugation in `S₄ ≀ C₂` -/

theorem conj_inl (q p : Perm (Fin 4) × Perm (Fin 4)) :
    (inl q : W4) * inl p * (inl q)⁻¹ = inl (q * p * q⁻¹) := by
  rw [← map_inv, inl_mul_inl, inl_mul_inl]

theorem conj_gS (p : Perm (Fin 4) × Perm (Fin 4)) :
    gS * inl p * gS⁻¹ = inl (p.2, p.1) := by
  rw [gS, ← map_inv (inr : Multiplicative (ZMod 2) →* W4), ← inl_aut, swapAut_gen]

theorem conj_gTgS (p : Perm (Fin 4) × Perm (Fin 4)) :
    (gT * gS) * inl p * (gT * gS)⁻¹ =
      inl (tauLoc * p.2 * tauLoc⁻¹, tauLoc * p.1 * tauLoc⁻¹) := by
  rw [show (gT * gS) * inl p * (gT * gS)⁻¹ = gT * (gS * inl p * gS⁻¹) * gT⁻¹ by group,
    conj_gS, gT, conj_inl]
  rfl

theorem gA_pow (k : ℕ) : gA ^ k = inl ((tLoc, tLoc) ^ k) := by
  rw [gA, inl_pow]

theorem gA_pow_three : gA ^ 3 = 1 := by
  rw [gA_pow, ← map_one (inl : Perm (Fin 4) × Perm (Fin 4) →* W4)]
  congr 1
  refine Prod.ext ?_ ?_ <;> decide

theorem comm_gA_of_inverts (g : W4) (hg : g * gA * g⁻¹ = gA⁻¹) : ⁅gA, g⁆ = gA ^ 2 := by
  rw [commutatorElement_def]
  calc gA * g * gA⁻¹ * g⁻¹ = gA * (g * gA * g⁻¹)⁻¹ := by group
    _ = gA ^ 2 := by rw [hg, inv_inv, pow_two]

theorem gA_eq_comm_sq (g : W4) (hg : g * gA * g⁻¹ = gA⁻¹) : gA = ⁅gA, g⁆ ^ 2 := by
  rw [comm_gA_of_inverts g hg, ← pow_mul]
  calc gA = gA ^ 3 * gA := by rw [gA_pow_three, one_mul]
    _ = gA ^ (2 * 2) := by rw [← pow_succ]

theorem gT_inverts : gT * gA * gT⁻¹ = gA⁻¹ := by
  rw [gT, gA, conj_inl, ← map_inv]
  congr 1
  refine Prod.ext ?_ ?_ <;> decide

theorem gTgS_inverts : (gT * gS) * gA * (gT * gS)⁻¹ = gA⁻¹ := by
  rw [gA, conj_gTgS, ← map_inv]
  congr 1
  refine Prod.ext ?_ ?_ <;> decide

/-! ## The base inside each class -/

instance VW_normal : VW.Normal := by
  constructor
  rintro v ⟨hv, hv1, hv2⟩ g
  have hvg : v = inl v.left := eq_inl_of_right v hv
  have hg : g = inl g.left * inr g.right := (inl_left_mul_inr_right g).symm
  have hφ : (swapAut (Perm (Fin 4)) g.right v.left).1 ∈ kleinSet ∧
      (swapAut (Perm (Fin 4)) g.right v.left).2 ∈ kleinSet := by
    rcases C2Wreath.cases g.right with h | h
    · rw [h, swapAut_one]
      exact ⟨hv1, hv2⟩
    · rw [h, swapAut_gen]
      exact ⟨hv2, hv1⟩
  have hconj : g * v * g⁻¹ =
      inl (g.left * swapAut (Perm (Fin 4)) g.right v.left * g.left⁻¹) := by
    have h1 : (inr g.right : W4) * inl v.left * (inr g.right)⁻¹ =
        inl (swapAut (Perm (Fin 4)) g.right v.left) := by
      rw [← map_inv (inr : Multiplicative (ZMod 2) →* W4), ← inl_aut]
    conv_lhs => rw [hvg, hg]
    calc inl g.left * inr g.right * inl v.left * (inl g.left * inr g.right)⁻¹
        = inl g.left * ((inr g.right : W4) * inl v.left * (inr g.right)⁻¹) *
            (inl g.left)⁻¹ := by group
      _ = _ := by rw [h1, conj_inl]
  rw [hconj]
  exact ⟨rfl, kleinSet_conj _ _ hφ.1, kleinSet_conj _ _ hφ.2⟩

theorem VW_le_Xc : VW ≤ Xc := by
  rw [Xc_eq_closure]
  exact fun x hx => Subgroup.subset_closure (Or.inl hx)

theorem VW_le_Xg : VW ≤ Xg := by
  rw [Xg_eq_closure]
  exact fun x hx => Subgroup.subset_closure (Or.inl hx)

theorem VW_le_Xs : VW ≤ Xs := by
  rw [Xs_eq_closure]
  exact fun x hx => Subgroup.subset_closure (Or.inl hx)

theorem gA_mem_Xc : gA ∈ Xc := by
  rw [Xc_eq_closure]
  exact Subgroup.subset_closure (Or.inr (Or.inl rfl))

theorem gA_mem_Xg : gA ∈ Xg := by
  rw [Xg_eq_closure]
  exact Subgroup.subset_closure (Or.inr (Or.inl rfl))

theorem gA_mem_Xs : gA ∈ Xs := by
  rw [Xs_eq_closure]
  exact Subgroup.subset_closure (Or.inr (Or.inl rfl))

theorem gS_mem_Xc : gS ∈ Xc := by
  rw [Xc_eq_closure]
  exact Subgroup.subset_closure (Or.inr (Or.inr rfl))

theorem gS_mem_Xs : gS ∈ Xs := by
  rw [Xs_eq_closure]
  exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr rfl)))

theorem gT_mem_Xs : gT ∈ Xs := by
  rw [Xs_eq_closure]
  exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))

theorem gTgS_mem_Xg : gT * gS ∈ Xg := by
  rw [Xg_eq_closure]
  exact Subgroup.subset_closure (Or.inr (Or.inr rfl))

/-- The base inside a class. -/
def VX (X : Subgroup W4) : Subgroup X := VW.subgroupOf X

theorem mem_VX {X : Subgroup W4} (v : X) : v ∈ VX X ↔ (v : W4) ∈ VW := Subgroup.mem_subgroupOf

instance VX_normal (X : Subgroup W4) : (VX X).Normal := Subgroup.Normal.subgroupOf inferInstance X

theorem VX_selfCentralizing (X : Subgroup W4) (hV : VW ≤ X) (x : X)
    (hx : ∀ v ∈ VX X, x * v = v * x) : x ∈ VX X :=
  VW_selfCentralizing _ (fun v hv => congrArg Subtype.val (hx ⟨v, hV hv⟩ hv))

theorem VX_comm (X : Subgroup W4) : ∀ v ∈ VX X, ∀ w ∈ VX X, v * w = w * v := by
  intro v hv w hw
  apply Subtype.ext
  obtain ⟨hvr, hv1, hv2⟩ := hv
  obtain ⟨hwr, hw1, hw2⟩ := hw
  show (v : W4) * w = (w : W4) * v
  rw [eq_inl_of_right (v : W4) hvr, eq_inl_of_right (w : W4) hwr, inl_mul_inl, inl_mul_inl]
  congr 1
  exact Prod.ext (kleinSet_comm _ hv1 _ hw1) (kleinSet_comm _ hv2 _ hw2)

/-- The diagonal three-cycle has no fixed points on the base. -/
theorem gA_free (X : Subgroup W4) (hA : gA ∈ X) (v : X) (hv : v ∈ VX X)
    (hfix : (⟨gA, hA⟩ : X) * v * (⟨gA, hA⟩ : X)⁻¹ = v) : v = 1 := by
  obtain ⟨hvr, hv1, hv2⟩ := hv
  have h : gA * (v : W4) * gA⁻¹ = v := by
    have := congrArg Subtype.val hfix
    simpa using this
  rw [eq_inl_of_right (v : W4) hvr, gA, conj_inl] at h
  have h' := inl_injective h
  have e1 := congrArg Prod.fst h'
  have e2 := congrArg Prod.snd h'
  simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv] at e1 e2
  rw [tLoc_eq_t3] at e1 e2
  have f1 := t3_fixedPointFree _ hv1 e1
  have f2 := t3_fixedPointFree _ hv2 e2
  apply Subtype.ext
  rw [eq_inl_of_right (v : W4) hvr]
  show inl (v : W4).left = inl 1
  congr 1
  exact Prod.ext f1 f2

/-- The base lies in the next derived term once `a` and the base lie in the
current one. -/
theorem VX_le_derived (X : Subgroup W4) (hA : gA ∈ X) (hV : VW ≤ X) (n : ℕ)
    (hAn : (⟨gA, hA⟩ : X) ∈ derivedSeries X n) (hVn : VX X ≤ derivedSeries X n) :
    VX X ≤ derivedSeries X (n + 1) := by
  intro v hv
  obtain ⟨hvr, hv1, hv2⟩ := hv
  obtain ⟨u1, hu1, e1⟩ := klein_comm_witness _ hv1
  obtain ⟨u2, hu2, e2⟩ := klein_comm_witness _ hv2
  have hu : (inl (u1, u2) : W4) ∈ VW := ⟨rfl, hu1, hu2⟩
  have hv' : v = ⁅(⟨gA, hA⟩ : X), (⟨inl (u1, u2), hV hu⟩ : X)⁆ := by
    apply Subtype.ext
    rw [show ((⁅(⟨gA, hA⟩ : X), (⟨inl (u1, u2), hV hu⟩ : X)⁆ : X) : W4) =
        ⁅gA, inl (u1, u2)⁆ by simp [commutatorElement_def]]
    rw [gA, ← map_commutatorElement, eq_inl_of_right (v : W4) hvr]
    congr 1
    refine Prod.ext ?_ ?_
    · show (v : W4).left.1 = ⁅tLoc, u1⁆
      rw [tLoc_eq_t3]
      exact e1.symm
    · show (v : W4).left.2 = ⁅tLoc, u2⁆
      rw [tLoc_eq_t3]
      exact e2.symm
  rw [hv']
  exact mem_derivedSeries_succ hAn (hVn hu)

/-- The absorption of every normal subgroup of the base. -/
theorem VX_absorbing (X : Subgroup W4) (hA : gA ∈ X) (n : ℕ)
    (hAn : (⟨gA, hA⟩ : X) ∈ derivedSeries X n) (hderived : derivedSeries X (n + 1) = VX X)
    (W : Subgroup X) (hW : W.Normal) (hWV : W ≤ VX X) :
    W ≤ ⁅derivedSeries X n, W⁆ :=
  DerivedHead.absorbing_of_fixedPointFree n _ hAn
    (by rw [hderived]; exact VX_comm X)
    (by rw [hderived]; exact gA_free X hA)
    W hW (hWV.trans hderived.ge)

/-! ## The separating character -/

/-- The first-coordinate character of the base. -/
def chiX (X : Subgroup W4) : VX X →* Multiplicative (ZMod 2) where
  toFun v := Multiplicative.ofAdd (offFirst ((v : X) : W4).left.1)
  map_one' := by
    show Multiplicative.ofAdd (offFirst 1) = 1
    decide
  map_mul' v w := by
    have hv : ((v : X) : W4) ∈ VW := v.2
    have hw : ((w : X) : W4) ∈ VW := w.2
    obtain ⟨hvr, hv1, _⟩ := hv
    obtain ⟨_, hw1, _⟩ := hw
    show Multiplicative.ofAdd (offFirst (((v : X) : W4) * ((w : X) : W4)).left.1) = _
    rw [left_mul_of_one _ _ hvr]
    simp only [Prod.fst_mul]
    rw [offFirst_mul _ hv1 _ hw1, ofAdd_add]

theorem offFirst_rotations : ∀ v ∈ kleinSet,
    (∀ k : Fin 3, offFirst (t3 ^ (k : ℕ) * v * (t3 ^ (k : ℕ))⁻¹) = 0) → v = 1 := by
  decide +kernel

theorem tau_conj_one : ∀ v ∈ kleinSet, tauLoc * v * tauLoc⁻¹ = 1 → v = 1 := by decide

theorem tau_conj_mem : ∀ v ∈ kleinSet, tauLoc * v * tauLoc⁻¹ ∈ kleinSet := by decide

/-- The character, its rotations and one block exchange `σ` of `X` separate the
base; `σ` exchanges the coordinates up to a conjugation `f` with trivial
kernel. -/
theorem chiX_separating (X : Subgroup W4) (hA : gA ∈ X) (σ : W4) (hσ : σ ∈ X)
    (f : Perm (Fin 4) → Perm (Fin 4)) (hf : ∀ v ∈ kleinSet, f v ∈ kleinSet)
    (hf1 : ∀ v ∈ kleinSet, f v = 1 → v = 1)
    (hconj : ∀ p : Perm (Fin 4) × Perm (Fin 4), σ * inl p * σ⁻¹ = inl (f p.2, f p.1))
    (v : VX X) (hv : ∀ q : X, chiX X (MulAut.conjNormal q v) = 1) : v = 1 := by
  have hvV : ((v : X) : W4) ∈ VW := v.2
  obtain ⟨hvr, hv1, hv2⟩ := hvV
  have hrot : ∀ (k : Fin 3) (p : Perm (Fin 4) × Perm (Fin 4)),
      gA ^ (k : ℕ) * inl p * (gA ^ (k : ℕ))⁻¹ =
        inl (t3 ^ (k : ℕ) * p.1 * (t3 ^ (k : ℕ))⁻¹, t3 ^ (k : ℕ) * p.2 * (t3 ^ (k : ℕ))⁻¹) := by
    intro k p
    rw [gA_pow, conj_inl, tLoc_eq_t3]
    rfl
  have hval : ∀ q : X, offFirst ((q : W4) * ((v : X) : W4) * (q : W4)⁻¹).left.1 = 0 := by
    intro q
    have := hv q
    change Multiplicative.ofAdd (offFirst ((q : W4) * ((v : X) : W4) * (q : W4)⁻¹).left.1) = 1
      at this
    exact Multiplicative.ofAdd.injective this
  have hvW : ((v : X) : W4) = inl ((v : X) : W4).left := eq_inl_of_right _ hvr
  have e1 : ((v : X) : W4).left.1 = 1 := by
    apply offFirst_rotations _ hv1
    intro k
    have := hval ⟨gA ^ (k : ℕ), X.pow_mem hA _⟩
    simp only at this
    rw [hvW, hrot] at this
    simpa [left_inl] using this
  have e2 : ((v : X) : W4).left.2 = 1 := by
    apply hf1 _ hv2
    apply offFirst_rotations _ (hf _ hv2)
    intro k
    have := hval ⟨gA ^ (k : ℕ) * σ, X.mul_mem (X.pow_mem hA _) hσ⟩
    simp only at this
    rw [hvW, mul_inv_rev, show gA ^ (k : ℕ) * σ * inl ((v : X) : W4).left *
        (σ⁻¹ * (gA ^ (k : ℕ))⁻¹) =
        gA ^ (k : ℕ) * (σ * inl ((v : X) : W4).left * σ⁻¹) * (gA ^ (k : ℕ))⁻¹ by group,
      hconj, hrot] at this
    simpa [left_inl] using this
  apply Subtype.ext
  apply Subtype.ext
  rw [hvW]
  show inl ((v : X) : W4).left = inl 1
  congr 1
  exact Prod.ext e1 e2

end TwoFourDiagonal
end SymmetricSubgroupAsymptotics
