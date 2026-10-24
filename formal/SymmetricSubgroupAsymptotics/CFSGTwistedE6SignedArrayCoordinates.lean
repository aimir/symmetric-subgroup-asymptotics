import SymmetricSubgroupAsymptotics.CFSGTwistedE6HeisenbergTwistCompatibility
import SymmetricSubgroupAsymptotics.CFSGQuadraticSignedFixedCoordinates

/-! Explicit fixed arrays for the actual E6 Heisenberg diagram permutation.
Its four fixed indices and three two-cycles are retained literally.
Compatibility of partner weights is an ordinary signed-action condition;
the actual root weights satisfy it by their checked matrix involution.
No full-field linearity of an arbitrary subgroup is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6SignedArrayCoordinates
open CFSGSerreOrdinaryTwists CFSGTwistedANaturalMatrices CFSGTwistedA2FixedField
open CFSGTwistedE6HeisenbergStableRootFamilies CFSGQuadraticSignedFixedCoordinates
open CFSGCommutingParameterTwist

def fixedIndex : Fin 4 → Fin 10 := ![0,1,5,7]
def pairIndex : Fin 3 → Fin 10 := ![2,3,6]

private theorem partner_fixedIndex (j : Fin 4) : partner (fixedIndex j) = fixedIndex j := by
  fin_cases j <;> rfl

private theorem sign_square {K : Type*} [CommRing K] {a : ℤ}
    (ha : a = 1 ∨ a = -1) : (a : K) * (a : K) = 1 := by
  rcases ha with rfl | rfl <;> simp

private theorem scalar_flip {K : Type*} [CommRing K] {s x y : K}
    (hs : s * s = 1) (h : x = s * y) : y = s * x := by
  calc
    y = (s * s) * y := by rw [hs, one_mul]
    _ = s * (s * y) := mul_assoc _ _ _
    _ = s * x := congrArg (fun z => s * z) h.symm

def arraySpace (q : CFSG.PrimePower) (w : Fin 10 → ℤ) :
    Submodule (fixedField q) (Fin 10 → q.Extension 2) where
  carrier := {v | ∀ i, v (partner i) = (w i : q.Extension 2) * definingFieldAutomorphism q 2 (v i)}
  zero_mem' := by intro i; simp only [Pi.zero_apply, map_zero, mul_zero]
  add_mem' ha hb := by
    intro i
    change _ + _ = (w i : q.Extension 2) * definingFieldAutomorphism q 2 (_ + _)
    rw [ha i, hb i, map_add, mul_add]
  smul_mem' c v hv := by
    intro i
    have hc : definingFieldAutomorphism q 2 (c : q.Extension 2) = (c : q.Extension 2) :=
      c.property
    change (c : q.Extension 2) * v (partner i) =
      (w i : q.Extension 2) * definingFieldAutomorphism q 2 ((c : q.Extension 2) * v i)
    rw [hv i, map_mul, hc]
    ring

theorem mem_arraySpace_iff (q : CFSG.PrimePower) (w : Fin 10 → ℤ)
    (v : Fin 10 → q.Extension 2) :
    v ∈ arraySpace q w ↔ coefficientMap (definingFieldAutomorphism q 2) partner w v = v := by
  constructor
  · intro hv
    ext j
    have hh := hv (partner.symm j)
    change v (partner (partner.symm j)) =
      (w (partner.symm j) : q.Extension 2) *
        definingFieldAutomorphism q 2 (v (partner.symm j)) at hh
    rw [partner.apply_symm_apply] at hh
    exact hh.symm
  · intro hv i
    have hh := congrArg (fun z : Fin 10 → q.Extension 2 => z (partner i)) hv
    change (w (partner.symm (partner i)) : q.Extension 2) *
      definingFieldAutomorphism q 2 (v (partner.symm (partner i))) = v (partner i) at hh
    rw [partner.symm_apply_apply] at hh
    exact hh.symm

def Data (q : CFSG.PrimePower) (w : Fin 10 → ℤ) :=
  (∀ j : Fin 4, signedLine q (w (fixedIndex j))) ×
    (∀ j : Fin 3, pairedSpace q (w (pairIndex j)))

def pack (q : CFSG.PrimePower) (w : Fin 10 → ℤ)
    (hw : ∀ i, w i = 1 ∨ w i = -1) (v : arraySpace q w) : Data q w :=
  (fun j => ⟨v.val (fixedIndex j), by
    have hh := v.property (fixedIndex j)
    rw [partner_fixedIndex] at hh
    exact scalar_flip (sign_square (K := q.Extension 2) (hw (fixedIndex j))) hh⟩,
   fun j => ⟨(v.val (pairIndex j), v.val (partner (pairIndex j))), v.property (pairIndex j)⟩)

def values (q : CFSG.PrimePower) (w : Fin 10 → ℤ) (d : Data q w) : Fin 10 → q.Extension 2 :=
  ![(d.1 0).val, (d.1 1).val, (d.2 0).val.1, (d.2 1).val.1,
    (d.2 0).val.2, (d.1 2).val, (d.2 2).val.1, (d.1 3).val,
    (d.2 2).val.2, (d.2 1).val.2]

private theorem reverse_pair (q : CFSG.PrimePower) (a b : ℤ)
    (hab : (b : q.Extension 2) * (a : q.Extension 2) = 1) (v : pairedSpace q a) :
    v.val.1 = (b : q.Extension 2) * definingFieldAutomorphism q 2 v.val.2 := by
  have hv : v.val.2 = (a : q.Extension 2) * definingFieldAutomorphism q 2 v.val.1 :=
    v.property
  have hs : definingFieldAutomorphism q 2 (definingFieldAutomorphism q 2 v.val.1) = v.val.1 :=
    extension_two_pow_twice q v.val.1
  rw [hv, map_mul, map_intCast, hs, ← mul_assoc, hab, one_mul]

theorem values_mem (q : CFSG.PrimePower) (w : Fin 10 → ℤ)
    (hw : ∀ i, w i = 1 ∨ w i = -1)
    (hc : ∀ i, (w (partner i) : q.Extension 2) * (w i : q.Extension 2) = 1)
    (d : Data q w) : values q w d ∈ arraySpace q w := by
  intro i
  fin_cases i
  · change (d.1 0).val = (w 0 : q.Extension 2) * definingFieldAutomorphism q 2 (d.1 0).val
    exact scalar_flip (sign_square (K := q.Extension 2) (hw 0)) (d.1 0).property
  · change (d.1 1).val = (w 1 : q.Extension 2) * definingFieldAutomorphism q 2 (d.1 1).val
    exact scalar_flip (sign_square (K := q.Extension 2) (hw 1)) (d.1 1).property
  · change (d.2 0).val.2 = (w 2 : q.Extension 2) * definingFieldAutomorphism q 2 (d.2 0).val.1
    exact (d.2 0).property
  · change (d.2 1).val.2 = (w 3 : q.Extension 2) * definingFieldAutomorphism q 2 (d.2 1).val.1
    exact (d.2 1).property
  · change (d.2 0).val.1 = (w 4 : q.Extension 2) * definingFieldAutomorphism q 2 (d.2 0).val.2
    exact reverse_pair q (w 2) (w 4) (hc 2) (d.2 0)
  · change (d.1 2).val = (w 5 : q.Extension 2) * definingFieldAutomorphism q 2 (d.1 2).val
    exact scalar_flip (sign_square (K := q.Extension 2) (hw 5)) (d.1 2).property
  · change (d.2 2).val.2 = (w 6 : q.Extension 2) * definingFieldAutomorphism q 2 (d.2 2).val.1
    exact (d.2 2).property
  · change (d.1 3).val = (w 7 : q.Extension 2) * definingFieldAutomorphism q 2 (d.1 3).val
    exact scalar_flip (sign_square (K := q.Extension 2) (hw 7)) (d.1 3).property
  · change (d.2 2).val.1 = (w 8 : q.Extension 2) * definingFieldAutomorphism q 2 (d.2 2).val.2
    exact reverse_pair q (w 6) (w 8) (hc 6) (d.2 2)
  · change (d.2 1).val.1 = (w 9 : q.Extension 2) * definingFieldAutomorphism q 2 (d.2 1).val.2
    exact reverse_pair q (w 3) (w 9) (hc 3) (d.2 1)

def dataEquiv (q : CFSG.PrimePower) (w : Fin 10 → ℤ)
    (hw : ∀ i, w i = 1 ∨ w i = -1)
    (hc : ∀ i, (w (partner i) : q.Extension 2) * (w i : q.Extension 2) = 1) :
    arraySpace q w ≃ Data q w where
  toFun := pack q w hw
  invFun d := ⟨values q w d, values_mem q w hw hc d⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  right_inv d := by
    apply Prod.ext
    · funext j
      apply Subtype.ext
      fin_cases j <;> rfl
    · funext j
      apply Subtype.ext
      fin_cases j <;> rfl

theorem arraySpace_card (q : CFSG.PrimePower) (w : Fin 10 → ℤ)
    (hw : ∀ i, w i = 1 ∨ w i = -1)
    (hc : ∀ i, (w (partner i) : q.Extension 2) * (w i : q.Extension 2) = 1) :
    Nat.card (arraySpace q w) = q.order ^ 10 := by
  rw [Nat.card_congr (dataEquiv q w hw hc)]
  have hline (j : Fin 4) : Nat.card (signedLine q (w (fixedIndex j))) = q.order :=
    signedLine_card q _ (hw _)
  have hpair (j : Fin 3) : Nat.card (pairedSpace q (w (pairIndex j))) = q.order ^ 2 :=
    pairedSpace_card q _
  simp only [Data, Nat.card_prod, Nat.card_pi, hline, hpair, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  ring

end SymmetricSubgroupAsymptotics.CFSGTwistedE6SignedArrayCoordinates
