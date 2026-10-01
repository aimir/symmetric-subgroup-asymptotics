import SymmetricSubgroupAsymptotics.Non2PreE7C2Wreath
import SymmetricSubgroupAsymptotics.Non2PreE7NaturalS4Group

/-!
# The literal normal menu and second derived head of natural `A₄ ≀ C₂`

`G = A₄ ≀ C₂ = (A₄ × A₄) ⋊ C₂` acts on the two blocks `Fin 4 ⊕ Fin 4`.  The
base `V = V₄ × V₄` is the kernel of the action on the six block pairings.
It is minimal normal and self-centralizing, `G'' = V`, and the
anti-diagonal three-cycle in `G'` acts on `V` without fixed points.  Hence:

* every nontrivial literal quotient is a quotient of the pairing image
  `C₃ ≀ C₂` on six points;
* onto maps to `G` use the common source `J''` and one character of `V`:
  `|Epi(J, G)| ≤ |Aut G| · 2^(b/2)`.
-/

set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics
namespace NaturalS4

open Equiv

/-- The literal elements of `A₄`. -/
def a4Set : Finset (Perm (Fin 4)) :=
  {1, swap 1 2 * swap 2 3, swap 1 2 * swap 1 3, swap 0 1 * swap 2 3, swap 0 1 * swap 1 2,
    swap 0 1 * swap 1 3, swap 0 1 * swap 0 2, swap 0 2 * swap 2 3, swap 0 2 * swap 1 3,
    swap 0 1 * swap 0 3, swap 0 2 * swap 0 3, swap 0 3 * swap 1 2}

theorem a4Set_mul : ∀ a b : Perm (Fin 4), a ∈ a4Set → b ∈ a4Set → a * b ∈ a4Set := by
  decide

theorem a4Set_inv : ∀ a : Perm (Fin 4), a ∈ a4Set → a⁻¹ ∈ a4Set := by decide

/-- The alternating group of degree four. -/
def a4 : Subgroup (Perm (Fin 4)) where
  carrier := {σ | σ ∈ a4Set}
  mul_mem' ha hb := a4Set_mul _ _ ha hb
  one_mem' := by decide
  inv_mem' ha := a4Set_inv _ ha

instance : DecidablePred (· ∈ a4) := fun σ => inferInstanceAs (Decidable (σ ∈ a4Set))

theorem t3_mem_a4Set : t3 ∈ a4Set := by decide

theorem kleinSet_sub_a4Set : ∀ v ∈ kleinSet, v ∈ a4Set := by decide

set_option maxRecDepth 8192 in
theorem a4_commutator_mem_klein : ∀ a ∈ a4Set, ∀ b ∈ a4Set, ⁅a, b⁆ ∈ kleinSet := by decide

theorem klein_comm_witness : ∀ v ∈ kleinSet, ∃ u ∈ kleinSet, ⁅t3, u⁆ = v := by decide

theorem klein_comm_witness_inv : ∀ v ∈ kleinSet, ∃ u ∈ kleinSet, ⁅t3⁻¹, u⁆ = v := by decide

theorem t3inv_fixedPointFree : ∀ v ∈ kleinSet, t3⁻¹ * v * t3⁻¹⁻¹ = v → v = 1 := by decide

theorem t3_fixedPointFree' : ∀ v ∈ kleinSet, t3 * v * t3⁻¹ = v → v = 1 := t3_fixedPointFree

theorem klein_a4_transitive : ∀ a ∈ kleinSet, a ≠ 1 → ∀ v ∈ kleinSet, v ≠ 1 →
    ∃ g ∈ a4Set, g * a * g⁻¹ = v := by decide

theorem t3_comm_ne_one : ∀ a ∈ kleinSet, a ≠ 1 → ⁅t3, a⁆ ≠ 1 := by decide

theorem c1_ne_one : c1 ≠ 1 := by decide

theorem offFirst_c2 : offFirst c2 = 1 := by decide

end NaturalS4

namespace A4WreathC2

open Equiv NaturalS4 C2Wreath SemidirectProduct

/-- The group `A₄`. -/
abbrev A := ↥NaturalS4.a4

/-- The two-block wreath product `A₄ ≀ C₂`. -/
abbrev G := C2Wreath.W A

instance : Finite G := Finite.of_equiv _ SemidirectProduct.equivProd.symm

def tA : A := ⟨t3, t3_mem_a4Set⟩

def ofKlein (v : Perm (Fin 4)) (hv : v ∈ kleinSet) : A := ⟨v, kleinSet_sub_a4Set v hv⟩

/-- The action on the six block pairings. -/
def blockPairing : G →* Perm (Fin 3 ⊕ Fin 3) := C2Wreath.action (pairing.comp a4.subtype)

/-- The natural action on the two blocks. -/
def natural : G →* Perm (Fin 4 ⊕ Fin 4) := C2Wreath.action a4.subtype

theorem natural_injective : Function.Injective natural :=
  C2Wreath.action_injective _ Subtype.val_injective

/-- The base `V₄ × V₄`. -/
def V : Subgroup G := blockPairing.ker

instance : V.Normal := MonoidHom.normal_ker _

theorem eq_inl_mul_inr (x : G) : x = inl x.left * inr x.right :=
  (inl_left_mul_inr_right x).symm

theorem eq_inl_of_right (x : G) (h : x.right = 1) : x = inl x.left := by
  conv_lhs => rw [eq_inl_mul_inr x, h, map_one, mul_one]

theorem sumCongr_eq_one_iff {f g : Perm (Fin 3)} : Perm.sumCongr f g = 1 ↔ f = 1 ∧ g = 1 := by
  constructor
  · intro h
    constructor
    · refine Equiv.ext fun x => ?_
      have := congrArg (fun σ : Perm (Fin 3 ⊕ Fin 3) => σ (Sum.inl x)) h
      simpa using this
    · refine Equiv.ext fun x => ?_
      have := congrArg (fun σ : Perm (Fin 3 ⊕ Fin 3) => σ (Sum.inr x)) h
      simpa using this
  · rintro ⟨rfl, rfl⟩
    exact Perm.sumCongr_one

theorem mem_V_iff (x : G) : x ∈ V ↔ x.right = 1 ∧
    ((x.left.1 : Perm (Fin 4)) ∈ kleinSet ∧ (x.left.2 : Perm (Fin 4)) ∈ kleinSet) := by
  rw [V, MonoidHom.mem_ker]
  conv_lhs => rw [eq_inl_mul_inr x]
  rcases C2Wreath.cases x.right with h | h
  · rw [h, map_one, mul_one, blockPairing, C2Wreath.action_inl, sumCongr_eq_one_iff]
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, true_and]
    rw [← MonoidHom.mem_ker, ← MonoidHom.mem_ker, ker_pairing]
    rfl
  · rw [h, map_mul, blockPairing, C2Wreath.action_inl, C2Wreath.action_inr_gen]
    simp only [C2Wreath.gen_ne_one, false_and, iff_false]
    intro hx
    have := congrArg (fun σ : Perm (Fin 3 ⊕ Fin 3) => σ (Sum.inl 0)) hx
    simp at this

theorem inl_mem_V (p : A × A) (h1 : (p.1 : Perm (Fin 4)) ∈ kleinSet)
    (h2 : (p.2 : Perm (Fin 4)) ∈ kleinSet) : (inl p : G) ∈ V := by
  rw [mem_V_iff]
  exact ⟨rfl, h1, h2⟩

theorem comm_inl (p q : A × A) : ⁅(inl p : G), (inl q : G)⁆ = (inl ⁅p, q⁆ : G) :=
  (map_commutatorElement (inl : A × A →* G) p q).symm

theorem prod_comm_fst (p q : A × A) : (⁅p, q⁆).1 = ⁅p.1, q.1⁆ := by
  simp [commutatorElement_def]

theorem prod_comm_snd (p q : A × A) : (⁅p, q⁆).2 = ⁅p.2, q.2⁆ := by
  simp [commutatorElement_def]

theorem coe_comm (a b : A) :
    ((⁅a, b⁆ : A) : Perm (Fin 4)) = ⁅(a : Perm (Fin 4)), (b : Perm (Fin 4))⁆ := by
  simp [commutatorElement_def]

/-! ## The derived series -/

theorem comm_inl_tA_gen :
    ⁅(inl (tA, 1) : G), (inr C2Wreath.gen : G)⁆ = (inl (tA, tA⁻¹) : G) := by
  rw [commutatorElement_def]
  have h1 : (inr C2Wreath.gen : G) * (inl (tA, 1))⁻¹ * (inr C2Wreath.gen)⁻¹ =
      inl (swapAut A C2Wreath.gen (tA, 1)⁻¹) := by
    rw [inl_aut, ← map_inv, ← map_inv, C2Wreath.gen_inv]
  calc (inl (tA, 1) : G) * inr C2Wreath.gen * (inl (tA, 1))⁻¹ * (inr C2Wreath.gen)⁻¹
      = inl (tA, 1) * (inr C2Wreath.gen * (inl (tA, 1))⁻¹ * (inr C2Wreath.gen)⁻¹) := by group
    _ = inl ((tA, 1) * swapAut A C2Wreath.gen (tA, 1)⁻¹) := by rw [h1, map_mul]
    _ = inl (tA, tA⁻¹) := by
        rw [C2Wreath.swapAut_gen]
        simp

theorem anti_mem : (inl (tA, tA⁻¹) : G) ∈ derivedSeries G 1 := by
  rw [← comm_inl_tA_gen]
  exact mem_derivedSeries_one _ _

theorem V_le_one : V ≤ derivedSeries G 1 := by
  intro v hv
  rw [mem_V_iff] at hv
  obtain ⟨hr, h1, h2⟩ := hv
  obtain ⟨u1, hu1, e1⟩ := klein_comm_witness _ h1
  obtain ⟨u2, hu2, e2⟩ := klein_comm_witness _ h2
  have hv' : v = ⁅(inl (tA, tA) : G), inl (ofKlein u1 hu1, ofKlein u2 hu2)⁆ := by
    rw [comm_inl, eq_inl_of_right v hr]
    congr 1
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [prod_comm_fst, coe_comm]
      exact e1.symm
    · rw [prod_comm_snd, coe_comm]
      exact e2.symm
  rw [hv']
  exact mem_derivedSeries_one _ _

theorem V_le_two : V ≤ derivedSeries G 2 := by
  intro v hv
  rw [mem_V_iff] at hv
  obtain ⟨hr, h1, h2⟩ := hv
  obtain ⟨u1, hu1, e1⟩ := klein_comm_witness _ h1
  obtain ⟨u2, hu2, e2⟩ := klein_comm_witness_inv _ h2
  have hv' : v = ⁅(inl (tA, tA⁻¹) : G), inl (ofKlein u1 hu1, ofKlein u2 hu2)⁆ := by
    rw [comm_inl, eq_inl_of_right v hr]
    congr 1
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [prod_comm_fst, coe_comm]
      exact e1.symm
    · rw [prod_comm_snd, coe_comm]
      exact e2.symm
  rw [hv']
  exact mem_derivedSeries_succ anti_mem (V_le_one (inl_mem_V _ hu1 hu2))

theorem derivedSeries_two : derivedSeries G 2 = V := by
  apply le_antisymm
  · have h1 : derivedSeries G 1 ≤ (rightHom : G →* Multiplicative (ZMod 2)).ker := by
      rw [derivedSeries_one]
      exact Abelianization.commutator_subset_ker _
    rw [derivedSeries_succ]
    refine (Subgroup.commutator_mono h1 h1).trans ?_
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hxr : x.right = 1 := hx
    have hyr : y.right = 1 := hy
    rw [eq_inl_of_right x hxr, eq_inl_of_right y hyr, comm_inl]
    apply inl_mem_V
    · rw [prod_comm_fst, coe_comm]
      exact a4_commutator_mem_klein _ x.left.1.2 _ y.left.1.2
    · rw [prod_comm_snd, coe_comm]
      exact a4_commutator_mem_klein _ x.left.2.2 _ y.left.2.2
  · exact V_le_two

/-! ## Centralizer, absorption and minimality -/

theorem inl_mul_inl (p q : A × A) : (inl p : G) * inl q = inl (p * q) := (map_mul _ p q).symm

theorem left_eq_of_inl_eq {p q : A × A} (h : (inl p : G) = inl q) : p = q :=
  inl_injective h

theorem V_selfCentralizing (x : G) (hx : ∀ v ∈ V, x * v = v * x) : x ∈ V := by
  have hk : ∀ v ∈ kleinSet, (1 : Perm (Fin 4)) ∈ kleinSet := fun _ _ => by decide
  rcases C2Wreath.cases x.right with h | h
  · rw [mem_V_iff]
    refine ⟨h, ?_, ?_⟩
    · have hc : ∀ v (hv : v ∈ kleinSet), (x.left.1 : Perm (Fin 4)) * v = v * x.left.1 := by
        intro v hv
        have := hx (inl (ofKlein v hv, 1))
          (inl_mem_V _ hv (by exact (by decide : ((1 : A) : Perm (Fin 4)) ∈ kleinSet)))
        rw [eq_inl_of_right x h, inl_mul_inl, inl_mul_inl] at this
        have := congrArg (fun p : A × A => (p.1 : Perm (Fin 4))) (left_eq_of_inl_eq this)
        simpa [ofKlein] using this
      exact centralizer_kleinSet _ (hc c1 (by decide)) (hc c2 (by decide)) (hc c3 (by decide))
    · have hc : ∀ v (hv : v ∈ kleinSet), (x.left.2 : Perm (Fin 4)) * v = v * x.left.2 := by
        intro v hv
        have := hx (inl (1, ofKlein v hv))
          (inl_mem_V _ (by exact (by decide : ((1 : A) : Perm (Fin 4)) ∈ kleinSet)) hv)
        rw [eq_inl_of_right x h, inl_mul_inl, inl_mul_inl] at this
        have := congrArg (fun p : A × A => (p.2 : Perm (Fin 4))) (left_eq_of_inl_eq this)
        simpa [ofKlein] using this
      exact centralizer_kleinSet _ (hc c1 (by decide)) (hc c2 (by decide)) (hc c3 (by decide))
  · exfalso
    have hv0 := hx (inl (ofKlein c1 (by decide), 1)) (inl_mem_V _ (by decide) (by decide))
    have := congrArg (fun y : G => (y.left.1 : Perm (Fin 4))) hv0
    simp only [mul_left', h, C2Wreath.swapAut_gen, left_inl, right_inl,
      C2Wreath.swapAut_one] at this
    simp [ofKlein] at this
    exact c1_ne_one this

theorem V_comm : ∀ v ∈ derivedSeries G 2, ∀ w ∈ derivedSeries G 2, v * w = w * v := by
  rw [derivedSeries_two]
  intro v hv w hw
  rw [mem_V_iff] at hv hw
  rw [eq_inl_of_right v hv.1, eq_inl_of_right w hw.1, inl_mul_inl, inl_mul_inl]
  congr 1
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · exact kleinSet_comm _ hv.2.1 _ hw.2.1
  · exact kleinSet_comm _ hv.2.2 _ hw.2.2

theorem anti_free : ∀ v ∈ derivedSeries G 2,
    (inl (tA, tA⁻¹) : G) * v * (inl (tA, tA⁻¹))⁻¹ = v → v = 1 := by
  rw [derivedSeries_two]
  intro v hv hfix
  rw [mem_V_iff] at hv
  rw [eq_inl_of_right v hv.1, ← map_inv, inl_mul_inl, inl_mul_inl] at hfix
  rw [eq_inl_of_right v hv.1]
  have h := left_eq_of_inl_eq hfix
  have h1 := congrArg (fun p : A × A => (p.1 : Perm (Fin 4))) h
  have h2 := congrArg (fun p : A × A => (p.2 : Perm (Fin 4))) h
  simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv, Subgroup.coe_mul,
    Subgroup.coe_inv, tA] at h1 h2
  have e1 := t3_fixedPointFree _ hv.2.1 h1
  have e2 := t3inv_fixedPointFree _ hv.2.2 (by simpa using h2)
  rw [← map_one (inl : A × A →* G)]
  congr 1
  exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)

theorem V_absorbing (W : Subgroup G) (hW : W.Normal) (hWV : W ≤ V) :
    W ≤ ⁅derivedSeries G 1, W⁆ :=
  DerivedHead.absorbing_of_fixedPointFree 1 _ anti_mem V_comm anti_free W hW
    (hWV.trans derivedSeries_two.ge)

theorem conj_inl_first (W : Subgroup G) (hW : W.Normal) (a : A)
    (ha : (a : Perm (Fin 4)) ∈ kleinSet) (ha1 : (a : Perm (Fin 4)) ≠ 1)
    (haW : (inl (a, 1) : G) ∈ W) (v : Perm (Fin 4)) (hv : v ∈ kleinSet) :
    (inl (ofKlein v hv, 1) : G) ∈ W := by
  by_cases hv1 : v = 1
  · have : (ofKlein v hv, (1 : A)) = 1 := Prod.ext (Subtype.ext hv1) rfl
    rw [this, map_one]
    exact W.one_mem
  obtain ⟨g, hg, hgv⟩ := klein_a4_transitive _ ha ha1 v hv hv1
  have hc := hW.conj_mem _ haW (inl (⟨g, hg⟩, 1))
  rw [← map_inv, inl_mul_inl, inl_mul_inl] at hc
  convert hc using 2
  refine Prod.ext (Subtype.ext ?_) ?_
  · simp [ofKlein, hgv]
  · simp

theorem swap_inl (p : A × A) :
    (inr C2Wreath.gen : G) * inl p * (inr C2Wreath.gen)⁻¹ = inl (p.2, p.1) := by
  rw [← map_inv (inr : Multiplicative (ZMod 2) →* G), ← inl_aut, C2Wreath.swapAut_gen]

theorem comm_mem (W : Subgroup G) (hW : W.Normal) {q : G} (hq : q ∈ W) (g : G) :
    ⁅g, q⁆ ∈ W := by
  rw [commutatorElement_def]
  exact W.mul_mem (hW.conj_mem _ hq g) (W.inv_mem hq)

theorem V_minimal (W : Subgroup G) (hW : W.Normal) (hWV : W ≤ V) : W = ⊥ ∨ W = V := by
  by_cases hb : W = ⊥
  · exact Or.inl hb
  right
  apply le_antisymm hWV
  obtain ⟨⟨w, hwW⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hb
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hwV := mem_V_iff w |>.mp (hWV hwW)
  -- one nontrivial first coordinate in `W`
  have hfirst : ∃ a : A, (a : Perm (Fin 4)) ∈ kleinSet ∧ (a : Perm (Fin 4)) ≠ 1 ∧
      (inl (a, 1) : G) ∈ W := by
    have hw : w = inl w.left := eq_inl_of_right w hwV.1
    by_cases ha : (w.left.1 : Perm (Fin 4)) = 1
    · have hb2 : (w.left.2 : Perm (Fin 4)) ≠ 1 := by
        intro hb2
        apply hw1'
        rw [hw, ← map_one (inl : A × A →* G)]
        congr 1
        exact Prod.ext (Subtype.ext ha) (Subtype.ext hb2)
      -- swap, then commute with the diagonal three-cycle
      have hs := hW.conj_mem _ hwW (inr C2Wreath.gen)
      rw [hw, swap_inl] at hs
      have hc := comm_mem W hW hs (inl (tA, 1))
      rw [comm_inl] at hc
      refine ⟨⁅tA, w.left.2⁆, ?_, ?_, ?_⟩
      · rw [coe_comm]
        exact a4_commutator_mem_klein _ t3_mem_a4Set _ w.left.2.2
      · rw [coe_comm]
        exact t3_comm_ne_one _ hwV.2.2 hb2
      · convert hc using 2
        refine Prod.ext ?_ ?_
        · rw [prod_comm_fst]
        · rw [prod_comm_snd, commutatorElement_one_left]
    · have hc := comm_mem W hW hwW (inl (tA, 1))
      rw [hw, comm_inl] at hc
      refine ⟨⁅tA, w.left.1⁆, ?_, ?_, ?_⟩
      · rw [coe_comm]
        exact a4_commutator_mem_klein _ t3_mem_a4Set _ w.left.1.2
      · rw [coe_comm]
        exact t3_comm_ne_one _ hwV.2.1 ha
      · convert hc using 2
        refine Prod.ext ?_ ?_
        · rw [prod_comm_fst]
        · rw [prod_comm_snd, commutatorElement_one_left]
  obtain ⟨a, ha, ha1, haW⟩ := hfirst
  intro v hv
  have hv' := (mem_V_iff v).mp hv
  rw [eq_inl_of_right v hv'.1]
  have hsplit : (inl v.left : G) =
      inl (ofKlein _ hv'.2.1, 1) * inl (1, ofKlein _ hv'.2.2) := by
    rw [inl_mul_inl]
    congr 1
  rw [hsplit]
  refine W.mul_mem (conj_inl_first W hW a ha ha1 haW _ _) ?_
  have h1 := conj_inl_first W hW a ha ha1 haW _ hv'.2.2
  have hs := hW.conj_mem _ h1 (inr C2Wreath.gen)
  rw [swap_inl] at hs
  exact hs

/-! ## The character and the cyclic-dual target -/

/-- The first-coordinate character of `V` with kernel `{1, c1} × V₄`. -/
def chi0 : V →* Multiplicative (ZMod 2) where
  toFun v := Multiplicative.ofAdd (offFirst ((v : G).left.1 : Perm (Fin 4)))
  map_one' := by
    show Multiplicative.ofAdd (offFirst 1) = 1
    decide
  map_mul' v w := by
    have hv := (mem_V_iff v).mp v.2
    have hw := (mem_V_iff w).mp w.2
    show Multiplicative.ofAdd (offFirst (((v : G) * w).left.1 : Perm (Fin 4))) = _
    rw [mul_left', hv.1, C2Wreath.swapAut_one]
    simp only [Prod.fst_mul, Subgroup.coe_mul]
    rw [offFirst_mul _ hv.2.1 _ hw.2.1, ofAdd_add]

theorem chi0_ne_one : chi0 ≠ 1 := by
  intro h
  have := DFunLike.congr_fun h ⟨inl (ofKlein c2 (by decide), 1), inl_mem_V _ (by decide) (by decide)⟩
  change Multiplicative.ofAdd (offFirst c2) = 1 at this
  rw [offFirst_c2] at this
  exact absurd this (by decide)

/-- `A₄ ≀ C₂` is a binary cyclic-dual target on the common source `J''`. -/
def target : DerivedHead.DerivedCyclicTarget G V 1 2 where
  derived_eq := derivedSeries_two
  character := chi0
  self_centralizing := V_selfCentralizing
  absorbing := V_absorbing
  separating := DerivedHead.separating_of_minimal V_minimal chi0 chi0_ne_one

/-- `|Epi(J, A₄ ≀ C₂)| ≤ |Aut| · 2^(b/2)` on every actual source. -/
theorem epi_card_le {b : ℕ} (J : Subgroup (Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J G) : ℝ) ≤
      (Nat.card (G ≃* G) : ℝ) * (2 : ℝ) ^ ((1 / 2 : ℝ) * b) :=
  target.epi_card_le_binary J

end A4WreathC2
end SymmetricSubgroupAsymptotics
