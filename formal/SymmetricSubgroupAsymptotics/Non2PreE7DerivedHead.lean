import SymmetricSubgroupAsymptotics.EpimorphismKernelLabels
import SymmetricSubgroupAsymptotics.PrimeAbelianization
import Mathlib.GroupTheory.Solvable

/-!
# One common derived source for onto maps

Let `Q` be a finite target and let `V = Q^(n+1)` be a term of its derived
series.  Fix an arbitrary source `J` and the SAME subgroup `F = J^(n+1)` for
every onto map `φ : J → Q`.  Onto maps carry `F` onto `V`.

This file proves the common kernel principle.  Suppose `V` is abelian,
self-centralizing, and absorbs every normal subgroup below it under the
previous derived term: `W ≤ [Q^(n), W]`.  Then the kernel of an onto map is
determined by its intersection with the common source `F`.  In particular
the second derived source `J''` controls all onto maps to natural `S₄`, and
the first derived source `J'` those to dihedral targets.

If moreover one character `χ` of `V` has conjugates separating `V`, the
restriction of `φ` to `F`, followed by `χ`, determines that intersection.
Therefore

`|Epi(J, Q)| ≤ |Hom(F, C_p)| · |Aut Q|`.

No top-map multiplier, independently chosen kernel of `J`, or splitting
assumption occurs.  The finer head count, which also uses the endomorphism
field of `V`, is in `Non2PreE7DerivedHeadCount`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DerivedHead

variable {J Q : Type*} [Group J] [Group Q]

/-! ## The general kernel principle -/

/-- A normal subgroup of the source whose image lies in a self-centralizing
`V = ψ(F)` and which is recovered on `F` is killed by `ψ` as soon as `φ` and
`ψ` have the same kernel on `F`. -/
theorem ker_le_of_inf_eq (F : Subgroup J) [hFn : F.Normal] (V : Subgroup Q)
    (φ ψ : J →* Q) (hψF : F.map ψ = V)
    (hcent : ∀ q : Q, (∀ v ∈ V, q * v = v * q) → q ∈ V)
    (hlift : ∀ K : Subgroup J, K.Normal → K.map ψ ≤ V → K.map ψ ≤ (K ⊓ F).map ψ)
    (h : φ.ker ⊓ F = ψ.ker ⊓ F) : φ.ker ≤ ψ.ker := by
  have hV : φ.ker.map ψ ≤ V := by
    rintro _ ⟨k, hk, rfl⟩
    apply hcent
    intro v hv
    rw [← hψF] at hv
    obtain ⟨f, hf, rfl⟩ := hv
    have hk1 : φ k = 1 := hk
    have hc : k * f * k⁻¹ * f⁻¹ ∈ φ.ker ⊓ F := by
      refine ⟨?_, F.mul_mem (hFn.conj_mem f hf k) (F.inv_mem hf)⟩
      show φ (k * f * k⁻¹ * f⁻¹) = 1
      simp [hk1]
    rw [h] at hc
    have h1 : ψ (k * f * k⁻¹ * f⁻¹) = 1 := hc.1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc ψ k * ψ f = (ψ k * ψ f * (ψ k)⁻¹ * (ψ f)⁻¹) * (ψ f * ψ k) := by group
      _ = ψ f * ψ k := by rw [h1, one_mul]
  have hK := hlift φ.ker inferInstance hV
  rw [h] at hK
  have hbot : (ψ.ker ⊓ F).map ψ = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact hx.1
  intro k hk
  have hk' : ψ k ∈ φ.ker.map ψ := ⟨k, hk, rfl⟩
  have hk'' := hK hk'
  rw [hbot] at hk''
  exact (Subgroup.mem_bot).mp hk''

/-- Equal kernels on the common source give equal kernels. -/
theorem ker_eq_of_inf_eq (F : Subgroup J) [F.Normal] (V : Subgroup Q)
    (φ ψ : J →* Q) (hφF : F.map φ = V) (hψF : F.map ψ = V)
    (hcent : ∀ q : Q, (∀ v ∈ V, q * v = v * q) → q ∈ V)
    (hliftφ : ∀ K : Subgroup J, K.Normal → K.map φ ≤ V → K.map φ ≤ (K ⊓ F).map φ)
    (hliftψ : ∀ K : Subgroup J, K.Normal → K.map ψ ≤ V → K.map ψ ≤ (K ⊓ F).map ψ)
    (h : φ.ker ⊓ F = ψ.ker ⊓ F) : φ.ker = ψ.ker :=
  le_antisymm (ker_le_of_inf_eq F V φ ψ hψF hcent hliftψ h)
    (ker_le_of_inf_eq F V ψ φ hφF hcent hliftφ h.symm)

/-! ## The derived-series recovery -/

/-- Absorption below the previous derived term gives recovery on the next
derived term of the source, for every normal subgroup and every onto map. -/
theorem derived_lift (n : ℕ)
    (habs : ∀ W : Subgroup Q, W.Normal → W ≤ derivedSeries Q (n + 1) →
      W ≤ ⁅derivedSeries Q n, W⁆)
    (ψ : J →* Q) (hψ : Function.Surjective ψ)
    (K : Subgroup J) (hK : K.Normal) (hKV : K.map ψ ≤ derivedSeries Q (n + 1)) :
    K.map ψ ≤ (K ⊓ derivedSeries J (n + 1)).map ψ := by
  have hW : (K.map ψ).Normal := hK.map ψ hψ
  have hstep : ∀ i : ℕ, i ≤ n + 1 → K.map ψ ≤ (K ⊓ derivedSeries J i).map ψ := by
    intro i
    induction i with
    | zero =>
      intro _
      simp [derivedSeries_zero]
    | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      calc K.map ψ ≤ ⁅derivedSeries Q n, K.map ψ⁆ := habs _ hW hKV
        _ ≤ ⁅derivedSeries Q i, (K ⊓ derivedSeries J i).map ψ⁆ :=
            Subgroup.commutator_mono (derivedSeries_antitone Q (show i ≤ n by omega)) hprev
        _ = ⁅(derivedSeries J i).map ψ, (K ⊓ derivedSeries J i).map ψ⁆ := by
            rw [map_derivedSeries_eq hψ]
        _ = (⁅derivedSeries J i, K ⊓ derivedSeries J i⁆).map ψ :=
            (Subgroup.map_commutator _ _ _).symm
        _ ≤ (K ⊓ derivedSeries J (i + 1)).map ψ := by
            apply Subgroup.map_mono
            refine le_inf ?_ ?_
            · exact (Subgroup.commutator_le_right _ _).trans inf_le_left
            · rw [derivedSeries_succ]
              exact Subgroup.commutator_mono le_rfl inf_le_right
  exact hstep (n + 1) le_rfl

/-- A fixed-point-free element of the previous derived term makes every
invariant subgroup of an abelian finite `V` absorbed. -/
theorem absorbing_of_fixedPointFree [Finite Q] (n : ℕ) (c : Q)
    (hc : c ∈ derivedSeries Q n)
    (hcomm : ∀ v ∈ derivedSeries Q (n + 1), ∀ v' ∈ derivedSeries Q (n + 1),
      v * v' = v' * v)
    (hfree : ∀ v ∈ derivedSeries Q (n + 1), c * v * c⁻¹ = v → v = 1)
    (W : Subgroup Q) (hW : W.Normal) (hWV : W ≤ derivedSeries Q (n + 1)) :
    W ≤ ⁅derivedSeries Q n, W⁆ := by
  -- the commutator map with `c` is an injective self-map of `W`
  let f : W → W := fun w => ⟨c * (w : Q) * c⁻¹ * (w : Q)⁻¹,
    W.mul_mem (hW.conj_mem _ w.2 c) (W.inv_mem w.2)⟩
  have hinj : Function.Injective f := by
    intro w w' hww
    have h1 : c * (w : Q) * c⁻¹ * (w : Q)⁻¹ = c * (w' : Q) * c⁻¹ * (w' : Q)⁻¹ :=
      congrArg Subtype.val hww
    have hwV := hWV w.2
    have hw'V := hWV w'.2
    -- `c` fixes `w * w'⁻¹`
    have hd : c * ((w : Q) * (w' : Q)⁻¹) * c⁻¹ = (w : Q) * (w' : Q)⁻¹ := by
      have hcw : c * (w : Q) * c⁻¹ ∈ derivedSeries Q (n + 1) :=
        (derivedSeries_normal Q (n + 1)).conj_mem _ hwV c
      have hcw' : c * (w' : Q) * c⁻¹ ∈ derivedSeries Q (n + 1) :=
        (derivedSeries_normal Q (n + 1)).conj_mem _ hw'V c
      have e1 : c * ((w : Q) * (w' : Q)⁻¹) * c⁻¹ =
          (c * (w : Q) * c⁻¹) * (c * (w' : Q) * c⁻¹)⁻¹ := by group
      rw [e1]
      -- from h1: (c w c⁻¹) w⁻¹ = (c w' c⁻¹) w'⁻¹
      have h2 : (c * (w : Q) * c⁻¹) * (c * (w' : Q) * c⁻¹)⁻¹ =
          ((w : Q) * (w' : Q)⁻¹) := by
        have hcomm1 := hcomm _ hwV _ (Subgroup.inv_mem _ hcw')
        have hcomm2 := hcomm _ (Subgroup.inv_mem _ hw'V) _ hcw
        have hcomm3 := hcomm _ hwV _ (Subgroup.inv_mem _ hw'V)
        calc (c * (w : Q) * c⁻¹) * (c * (w' : Q) * c⁻¹)⁻¹
            = (c * (w : Q) * c⁻¹ * (w : Q)⁻¹) * (w : Q) * (c * (w' : Q) * c⁻¹)⁻¹ := by
              group
          _ = (c * (w' : Q) * c⁻¹ * (w' : Q)⁻¹) * (w : Q) * (c * (w' : Q) * c⁻¹)⁻¹ := by
              rw [h1]
          _ = (c * (w' : Q) * c⁻¹) * ((w' : Q)⁻¹ * (w : Q)) * (c * (w' : Q) * c⁻¹)⁻¹ := by
              group
          _ = (c * (w' : Q) * c⁻¹) * ((w : Q) * (w' : Q)⁻¹) * (c * (w' : Q) * c⁻¹)⁻¹ := by
              rw [hcomm3]
          _ = (w : Q) * (w' : Q)⁻¹ := by
              have hx : (w : Q) * (w' : Q)⁻¹ ∈ derivedSeries Q (n + 1) :=
                Subgroup.mul_mem _ hwV (Subgroup.inv_mem _ hw'V)
              rw [hcomm _ hcw' _ hx]
              group
      exact h2
    have hmem : (w : Q) * (w' : Q)⁻¹ ∈ derivedSeries Q (n + 1) :=
      Subgroup.mul_mem _ (hWV w.2) (Subgroup.inv_mem _ (hWV w'.2))
    have h3 := hfree _ hmem hd
    apply Subtype.ext
    exact mul_inv_eq_one.mp h3
  have hsurj : Function.Surjective f := by
    letI : Finite W := inferInstance
    exact Finite.surjective_of_injective hinj
  intro w hw
  obtain ⟨u, hu⟩ := hsurj ⟨w, hw⟩
  have hw' : w = c * (u : Q) * c⁻¹ * (u : Q)⁻¹ := (congrArg Subtype.val hu).symm
  rw [hw']
  exact Subgroup.commutator_mem_commutator hc u.2

/-- A minimal normal `V` which is not centralized by the previous derived
term absorbs every normal subgroup below it. -/
theorem absorbing_of_minimal (n : ℕ)
    (hmin : ∀ W : Subgroup Q, W.Normal → W ≤ derivedSeries Q (n + 1) →
      W = ⊥ ∨ W = derivedSeries Q (n + 1))
    (hne : ⁅derivedSeries Q n, derivedSeries Q (n + 1)⁆ ≠ ⊥)
    (W : Subgroup Q) (hW : W.Normal) (hWV : W ≤ derivedSeries Q (n + 1)) :
    W ≤ ⁅derivedSeries Q n, W⁆ := by
  rcases hmin W hW hWV with h | h
  · rw [h]
    exact bot_le
  · have hn : (⁅derivedSeries Q n, derivedSeries Q (n + 1)⁆).Normal :=
      Subgroup.commutator_normal _ _
    have hle : ⁅derivedSeries Q n, derivedSeries Q (n + 1)⁆ ≤ derivedSeries Q (n + 1) :=
      Subgroup.commutator_le_right _ _
    rcases hmin _ hn hle with h' | h'
    · exact absurd h' hne
    · rw [h]
      exact h'.symm.le

/-! ## The restriction and the cyclic-dual label -/

/-- The restriction of a map to the common source, landing in `V`. -/
def restriction (F : Subgroup J) (V : Subgroup Q) (φ : J →* Q) (hφ : F.map φ = V) :
    F →* V :=
  (φ.comp F.subtype).codRestrict V (fun f => by
    rw [← hφ]
    exact ⟨f, f.2, rfl⟩)

@[simp] theorem restriction_apply (F : Subgroup J) (V : Subgroup Q) (φ : J →* Q)
    (hφ : F.map φ = V) (f : F) :
    ((restriction F V φ hφ f : V) : Q) = φ f := rfl

/-- The cyclic-dual kernel test: an element of the common source dies iff all
its conjugates die under the single label. -/
theorem restriction_eq_one_iff (F : Subgroup J) [hFn : F.Normal] (V : Subgroup Q)
    [hVn : V.Normal] {p : ℕ} (χ : V →* Multiplicative (ZMod p))
    (hsep : ∀ v : V, (∀ q : Q, χ (MulAut.conjNormal q v) = 1) → v = 1)
    (φ : J →* Q) (hφ : Function.Surjective φ) (hφF : F.map φ = V) (f : F) :
    φ f = 1 ↔ ∀ g : J, χ (restriction F V φ hφF (MulAut.conjNormal g f)) = 1 := by
  constructor
  · intro hf g
    have : restriction F V φ hφF (MulAut.conjNormal g f) = 1 := by
      apply Subtype.ext
      simp [restriction_apply, hf]
    rw [this, map_one]
  · intro h
    have hv := hsep (restriction F V φ hφF f) (fun q => by
      obtain ⟨g, rfl⟩ := hφ q
      have heq : restriction F V φ hφF (MulAut.conjNormal g f) =
          MulAut.conjNormal (φ g) (restriction F V φ hφF f) := by
        apply Subtype.ext
        simp [restriction_apply]
      rw [← heq]
      exact h g)
    exact congrArg Subtype.val hv

/-- **The cyclic-dual onto bound.**  One character of `V` with separating
conjugates, one common source `F`, recovery on `F`, and a self-centralizing
`V` give `|Epi(J, Q)| ≤ |Hom(F, C_p)| · |Aut Q|`. -/
theorem epi_card_le_characters [Finite J] [Finite Q] {p : ℕ} [NeZero p]
    (F : Subgroup J) [F.Normal] (V : Subgroup Q) [V.Normal]
    (χ : V →* Multiplicative (ZMod p))
    (hsep : ∀ v : V, (∀ q : Q, χ (MulAut.conjNormal q v) = 1) → v = 1)
    (hcent : ∀ q : Q, (∀ v ∈ V, q * v = v * q) → q ∈ V)
    (hF : ∀ φ : GroupEpimorphism J Q, F.map φ.1 = V)
    (hlift : ∀ φ : GroupEpimorphism J Q, ∀ K : Subgroup J, K.Normal →
      K.map φ.1 ≤ V → K.map φ.1 ≤ (K ⊓ F).map φ.1) :
    Nat.card (GroupEpimorphism J Q) ≤
      Nat.card (F →* Multiplicative (ZMod p)) * Nat.card (Q ≃* Q) := by
  letI : Finite (F →* Multiplicative (ZMod p)) :=
    Finite.of_injective (fun f : F →* Multiplicative (ZMod p) =>
      (f : F → Multiplicative (ZMod p))) DFunLike.coe_injective
  let label : GroupEpimorphism J Q → (F →* Multiplicative (ZMod p)) :=
    fun φ => χ.comp (restriction F V φ.1 (hF φ))
  refine groupEpimorphism_card_le_kernel_labels label ?_
  intro φ ψ hl
  apply ker_eq_of_inf_eq F V φ.1 ψ.1 (hF φ) (hF ψ) hcent (hlift φ) (hlift ψ)
  ext x
  simp only [Subgroup.mem_inf, MonoidHom.mem_ker]
  constructor
  · rintro ⟨hx, hxF⟩
    refine ⟨?_, hxF⟩
    have h1 := (restriction_eq_one_iff F V χ hsep φ.1 φ.2 (hF φ) ⟨x, hxF⟩).mp hx
    have h2 : ∀ g : J, χ (restriction F V ψ.1 (hF ψ) (MulAut.conjNormal g ⟨x, hxF⟩)) = 1 := by
      intro g
      have := h1 g
      have hlg := DFunLike.congr_fun hl (MulAut.conjNormal g ⟨x, hxF⟩)
      simp only [label, MonoidHom.comp_apply] at hlg
      rw [← hlg]
      exact this
    exact (restriction_eq_one_iff F V χ hsep ψ.1 ψ.2 (hF ψ) ⟨x, hxF⟩).mpr h2
  · rintro ⟨hx, hxF⟩
    refine ⟨?_, hxF⟩
    have h1 := (restriction_eq_one_iff F V χ hsep ψ.1 ψ.2 (hF ψ) ⟨x, hxF⟩).mp hx
    have h2 : ∀ g : J, χ (restriction F V φ.1 (hF φ) (MulAut.conjNormal g ⟨x, hxF⟩)) = 1 := by
      intro g
      have := h1 g
      have hlg := DFunLike.congr_fun hl (MulAut.conjNormal g ⟨x, hxF⟩)
      simp only [label, MonoidHom.comp_apply] at hlg
      rw [hlg]
      exact this
    exact (restriction_eq_one_iff F V χ hsep φ.1 φ.2 (hF φ) ⟨x, hxF⟩).mpr h2

/-! ## The derived-series target -/

/-- A target whose `(n+1)`-st derived term is a literal subgroup `V` which is
abelian, self-centralizing, absorbing below the `n`-th term, and has one
separating character. -/
structure DerivedCyclicTarget (Q : Type*) [Group Q] (V : Subgroup Q) [V.Normal]
    (n p : ℕ) where
  derived_eq : derivedSeries Q (n + 1) = V
  character : V →* Multiplicative (ZMod p)
  self_centralizing : ∀ q : Q, (∀ v ∈ V, q * v = v * q) → q ∈ V
  absorbing : ∀ W : Subgroup Q, W.Normal → W ≤ V → W ≤ ⁅derivedSeries Q n, W⁆
  separating : ∀ v : V, (∀ q : Q, character (MulAut.conjNormal q v) = 1) → v = 1

instance derivedSeries_normal_inst (G : Type*) [Group G] (k : ℕ) :
    (derivedSeries G k).Normal :=
  derivedSeries_normal G k

/-- The derived recovery in terms of a literal `V = Q^(n+1)`. -/
theorem derived_lift_of_eq (n : ℕ) {V : Subgroup Q} (hV : derivedSeries Q (n + 1) = V)
    (habs : ∀ W : Subgroup Q, W.Normal → W ≤ V → W ≤ ⁅derivedSeries Q n, W⁆)
    (ψ : J →* Q) (hψ : Function.Surjective ψ)
    (K : Subgroup J) (hK : K.Normal) (hKV : K.map ψ ≤ V) :
    K.map ψ ≤ (K ⊓ derivedSeries J (n + 1)).map ψ :=
  derived_lift n (fun W hW hWV => habs W hW (hWV.trans hV.le)) ψ hψ K hK (hKV.trans hV.ge)

namespace DerivedCyclicTarget

variable {V : Subgroup Q} [V.Normal] {n p : ℕ}

/-- `|Epi(J, Q)| ≤ |Hom(J^(n+1), C_p)| · |Aut Q|`. -/
theorem epi_card_le (D : DerivedCyclicTarget Q V n p) [Finite J] [Finite Q] [NeZero p] :
    Nat.card (GroupEpimorphism J Q) ≤
      Nat.card (derivedSeries J (n + 1) →* Multiplicative (ZMod p)) *
        Nat.card (Q ≃* Q) :=
  epi_card_le_characters (derivedSeries J (n + 1)) V
    D.character D.separating D.self_centralizing
    (fun φ => (map_derivedSeries_eq φ.2 (n + 1)).trans D.derived_eq)
    (fun φ K hK hKV => derived_lift_of_eq n D.derived_eq D.absorbing φ.1 φ.2 K hK hKV)

end DerivedCyclicTarget

/-- A nontrivial character of a minimal normal `V` separates `V`. -/
theorem separating_of_minimal {V : Subgroup Q} [hVn : V.Normal] {p : ℕ}
    (hmin : ∀ W : Subgroup Q, W.Normal → W ≤ V → W = ⊥ ∨ W = V)
    (χ : V →* Multiplicative (ZMod p)) (hχ : χ ≠ 1) (v : V)
    (hv : ∀ q : Q, χ (MulAut.conjNormal q v) = 1) : v = 1 := by
  -- the kernel core of `χ` is a normal subgroup of `Q` below `V`
  let S : Subgroup Q :=
    { carrier := {x | ∃ hx : x ∈ V, ∀ q : Q, χ (MulAut.conjNormal q ⟨x, hx⟩) = 1}
      one_mem' := ⟨V.one_mem, fun q => by
        have : MulAut.conjNormal q (⟨1, V.one_mem⟩ : V) = 1 := map_one _
        rw [this, map_one]⟩
      mul_mem' := by
        rintro a b ⟨ha, hA⟩ ⟨hb, hB⟩
        refine ⟨V.mul_mem ha hb, fun q => ?_⟩
        have : MulAut.conjNormal q (⟨a * b, V.mul_mem ha hb⟩ : V) =
            MulAut.conjNormal q ⟨a, ha⟩ * MulAut.conjNormal q ⟨b, hb⟩ := by
          rw [← map_mul]
          rfl
        rw [this, map_mul, hA q, hB q, one_mul]
      inv_mem' := by
        rintro a ⟨ha, hA⟩
        refine ⟨V.inv_mem ha, fun q => ?_⟩
        have : MulAut.conjNormal q (⟨a⁻¹, V.inv_mem ha⟩ : V) =
            (MulAut.conjNormal q ⟨a, ha⟩)⁻¹ := by
          rw [← map_inv]
          rfl
        rw [this, map_inv, hA q, inv_one] }
  have hSn : S.Normal := by
    constructor
    rintro x ⟨hx, hX⟩ g
    refine ⟨hVn.conj_mem x hx g, fun q => ?_⟩
    have : MulAut.conjNormal q (⟨g * x * g⁻¹, hVn.conj_mem x hx g⟩ : V) =
        MulAut.conjNormal (q * g) ⟨x, hx⟩ := by
      apply Subtype.ext
      simp [mul_assoc]
    rw [this]
    exact hX (q * g)
  have hSV : S ≤ V := fun x hx => hx.1
  rcases hmin S hSn hSV with h | h
  · have hvS : (v : Q) ∈ S := ⟨v.2, hv⟩
    rw [h] at hvS
    exact Subtype.ext ((Subgroup.mem_bot).mp hvS)
  · exfalso
    apply hχ
    ext w
    have hwS : (w : Q) ∈ S := by
      rw [h]
      exact w.2
    obtain ⟨_, hW⟩ := hwS
    have := hW 1
    simpa using this

end DerivedHead
end SymmetricSubgroupAsymptotics
