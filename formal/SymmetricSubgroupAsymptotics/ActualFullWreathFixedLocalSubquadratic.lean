import SymmetricSubgroupAsymptotics.ActualFullWreathFiniteChiefCount
import SymmetricSubgroupAsymptotics.LMMFixedLocalChiefCostNumerics
import SymmetricSubgroupAsymptotics.LMMHomogeneousSupportNumerics

/-! Every fixed actual finite local group has a uniformly subquadratic
full-component wreath-family count, over ALL faithful transitive tops.
The chief trace and all layer bounds are produced internally. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Filter
open scoped Topology
namespace SymmetricSubgroupAsymptotics.ActualFullWreathFixedLocalSubquadratic
open LMMFixedLocalChiefCostNumerics LMMHomogeneousSupportNumerics
open ActualFullWreathFiniteChiefCount ActualFullWreathFamily

local instance autFinite {T : Type} [Group T] [Finite T] : Finite (T ≃* T) :=
  Finite.of_injective (fun f : T ≃* T => (f : T → T)) DFunLike.coe_injective

private theorem eventual_mul (f g : ℕ → ℕ)
    (hf : ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℕ in atTop, (f t : ℝ) ≤ (2 : ℝ)^(ε*(t : ℝ)^2))
    (hg : ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℕ in atTop, (g t : ℝ) ≤ (2 : ℝ)^(ε*(t : ℝ)^2))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, (f t*g t : ℝ) ≤ (2 : ℝ)^(ε*(t : ℝ)^2) := by
  filter_upwards [hf (ε/2) (by positivity),hg (ε/2) (by positivity)] with t ht hu
  calc
    _ ≤ (2 : ℝ)^((ε/2)*(t : ℝ)^2)*(2 : ℝ)^((ε/2)*(t : ℝ)^2) :=
      mul_le_mul ht hu (Nat.cast_nonneg _) (by positivity)
    _ = _ := by
      rw [←Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

theorem fixed_support_eventually (k u : ℕ) (hu : 1 ≤ u) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, (supportCount (t*k) u : ℝ) ≤ (2 : ℝ)^(ε*(t : ℝ)^2) := by
  let r : ℕ := 2^(k+1)
  have hr : 2 ≤ r := by
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (show 1 ≤ k+1 by omega)
    simpa only [pow_one] using hh
  have hrp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hlogr : Real.logb 2 (r : ℝ) = (k : ℝ)+1 := by
    simp only [r,Nat.cast_pow,Nat.cast_ofNat,Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),Nat.cast_add,Nat.cast_one,mul_one]
  let A := Real.logb 2 (u : ℝ)
  have hA : 0 ≤ A := Real.logb_nonneg (by norm_num) (by exact_mod_cast hu : (1 : ℝ) ≤ u)
  have hfactor : 1 ≤ (r : ℝ)*(Real.logb 2 (r : ℝ))^3 := by
    rw [hlogr]
    apply one_le_mul_of_one_le_of_one_le
      (by exact_mod_cast (show 1 ≤ r by omega))
    exact one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hauto : Real.logb 2 (u : ℝ) ≤ A*(r : ℝ)*(Real.logb 2 (r : ℝ))^3 := by
    convert le_mul_of_one_le_right hA hfactor using 1 <;> ring
  obtain ⟨N,hN⟩ := uniform_supportCount A hA (ε/(r : ℝ)^2) (by positivity)
  filter_upwards [eventually_ge_atTop N,eventually_ge_atTop 2] with t ht htwo
  have hmul : (t*k : ℕ) ≤ t*(k+1) := Nat.mul_le_mul_left t (by omega)
  have hm : ((t*k : ℕ) : ℝ) ≤ (t : ℝ)*Real.logb 2 (r : ℝ) := by
    rw [hlogr]
    exact_mod_cast hmul
  have hh := hN r t (t*k) u hr htwo hu hm hauto
    (ht.trans (Nat.le_mul_of_pos_left t (by omega)))
  have heq : (ε/(r : ℝ)^2)*((r*t : ℕ) : ℝ)^2 = ε*(t : ℝ)^2 := by
    push_cast
    field_simp [hrp.ne'] <;> ring
  simpa only [heq] using hh

theorem elementary_multiplier_eventually (a b s : ℕ) (hb : 1 ≤ b) (hs : 1 ≤ s)
    (c : ℝ) (hc : 0 ≤ c) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop,
      (Charge.multiplier c t (.elementary a b s) : ℝ) ≤ (2 : ℝ)^(ε*(t : ℝ)^2) := by
  have hbnat : 0 < b := by omega
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast hbnat
  have hlog : 0 ≤ Real.logb 2 (b : ℝ) := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast hb : (1 : ℝ) ≤ b)
  filter_upwards [ceil_charge_eventually a c (Real.logb 2 (b : ℝ)) hc hlog s hs ε hε] with t ht
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
    (by dsimp only [Charge.multiplier]; positivity :
      (0 : ℝ) < (Charge.multiplier c t (.elementary a b s) : ℝ))).mp
  simpa only [Charge.multiplier,ActualFullWreathElementaryRecurrence.exponentCeiling,
    Nat.cast_pow,Real.logb_pow] using ht

theorem simple_multiplier_eventually (k b u s : ℕ) (hb : 1 ≤ b) (hu : 1 ≤ u) (hs : 1 ≤ s)
    (c : ℝ) (hc : 0 ≤ c) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop,
      (Charge.multiplier c t (.simple k b u s) : ℝ) ≤ (2 : ℝ)^(ε*(t : ℝ)^2) := by
  have hbnat : 0 < b := by omega
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast hbnat
  have hlog : 0 ≤ (k : ℝ)*Real.logb 2 (b : ℝ) := mul_nonneg (Nat.cast_nonneg _)
    (Real.logb_nonneg (by norm_num) (by exact_mod_cast hb : (1 : ℝ) ≤ b))
  have hlift : ∀ δ : ℝ, 0 < δ → ∀ᶠ t : ℕ in atTop,
      ((b^((t*k)*Nat.ceil (c*WeakTransitiveDegreeInduction.rate (s*t))) : ℕ) : ℝ) ≤
        (2 : ℝ)^(δ*(t : ℝ)^2) := by
    intro δ hδ
    filter_upwards [ceil_charge_eventually 0 c ((k : ℝ)*Real.logb 2 (b : ℝ))
      hc hlog s hs δ hδ] with t ht
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (by positivity)).mp
    rw [Nat.cast_pow,Real.logb_pow]
    simpa only [Nat.cast_mul,Nat.cast_zero,zero_mul,mul_zero,zero_div,zero_add,mul_assoc,mul_left_comm,mul_comm] using ht
  have hh := eventual_mul (fun t => supportCount (t*k) u)
    (fun t => b^((t*k)*Nat.ceil (c*WeakTransitiveDegreeInduction.rate (s*t))))
    (fixed_support_eventually k u hu) hlift ε hε
  simpa only [Charge.multiplier,ActualFullWreathSimpleKernelRecurrence.multiplier,supportCount,Nat.cast_mul] using hh

theorem trace_product_eventually (c : ℝ) (hc : 0 ≤ c) {R : LocalGroup} {charges : List Charge}
    (h : Trace R charges) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, ((charges.map (Charge.multiplier c t)).prod : ℝ) ≤
      (2 : ℝ)^(ε*(t : ℝ)^2) := by
  induction h generalizing ε with
  | terminal R hR =>
      exact Filter.Eventually.of_forall (fun t => by
        simp only [List.map_nil,List.prod_nil,Nat.cast_one]
        exact Real.one_le_rpow (by norm_num) (mul_nonneg hε.le (sq_nonneg _)))
  | elementary R S phi hphi C charges next ih =>
      have hh := eventual_mul (fun t => Charge.multiplier c t
        (.elementary (Module.finrank (ZMod C.p) C.V) (Nat.card phi.ker) (Nat.card S.Carrier)))
        (fun t => (charges.map (Charge.multiplier c t)).prod)
        (elementary_multiplier_eventually _ _ _ Nat.card_pos Nat.card_pos c hc)
        (fun δ hδ => ih δ hδ) ε hε
      simpa only [List.map_cons,List.prod_cons,Nat.cast_mul] using hh
  | simple R S T k phi hphi e hZ charges next ih =>
      have hh := eventual_mul (fun t => Charge.multiplier c t
        (.simple k (Nat.card T) (Nat.card (T ≃* T)) (Nat.card S.Carrier)))
        (fun t => (charges.map (Charge.multiplier c t)).prod)
        (simple_multiplier_eventually _ _ _ _ Nat.card_pos Nat.card_pos Nat.card_pos c hc)
        (fun δ hδ => ih δ hδ) ε hε
      simpa only [List.map_cons,List.prod_cons,Nat.cast_mul] using hh

theorem fixed_local_family_eventually (hCFSG : CFSG.CFSGClassification) (R : LocalGroup)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (Q I : Type) [Group Q] [Finite Q] [Fintype I] [Nonempty I]
      [MulAction Q I] [FaithfulSMul Q I] [MulAction.IsPretransitive Q I],
      2 ≤ Nat.card I → N ≤ Nat.card I →
      (Nat.card (Family R.Carrier Q I) : ℝ) ≤ (2 : ℝ)^(ε*(Nat.card I : ℝ)^2) := by
  obtain ⟨c,charges,hc,htrace,hbound⟩ := exists_uniform_chief_product hCFSG R
  obtain ⟨N,hN⟩ := eventually_atTop.mp (trace_product_eventually c (by linarith only [hc]) htrace ε hε)
  refine ⟨N,?_⟩
  intro Q I _ _ _ _ _ _ _ htwo hlarge
  have hh : (Nat.card (Family R.Carrier Q I) : ℝ) ≤
      ((charges.map (Charge.multiplier c (Nat.card I))).prod : ℝ) := by
    exact_mod_cast hbound Q I htwo
  exact hh.trans (hN (Nat.card I) hlarge)

/-- The threshold depends only on the actual finite local group and ε.
Finiteness of the top and nonemptiness of the point set are derived from
the faithful finite action and the chosen threshold. -/
theorem fixed_local_group_subquadratic (hCFSG : CFSG.CFSGClassification)
    (R : Type) [Group R] [Finite R] (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ,∀ (Q I : Type) [Group Q] [Fintype I]
      [MulAction Q I] [FaithfulSMul Q I] [MulAction.IsPretransitive Q I],
      N≤Nat.card I →
      (Nat.card (Family R Q I) : ℝ)≤(2 : ℝ)^(ε*(Nat.card I : ℝ)^2) := by
  obtain ⟨N,hN⟩ := fixed_local_family_eventually hCFSG (ofType R) ε hε
  refine ⟨max 2 N,?_⟩
  intro Q I _ _ _ _ _ hlarge
  have htwo : 2≤Nat.card I := (le_max_left 2 N).trans hlarge
  letI : Nontrivial I := Finite.one_lt_card_iff_nontrivial.mp (by omega : 1<Nat.card I)
  letI : Finite Q := Finite.of_injective (MulAction.toPermHom Q I) MulAction.toPerm_injective
  exact hN Q I htwo ((le_max_right 2 N).trans hlarge)

end SymmetricSubgroupAsymptotics.ActualFullWreathFixedLocalSubquadratic
