import SymmetricSubgroupAsymptotics.LabelledTransitiveBlockCode
import Mathlib.Data.Finite.Perm

/-! Cardinality of the actual reversible labelled block code.
Only compatible widths contribute. Their chart count is n!, and the
single top count is charged to the sum of strictly smaller degrees.
No asymptotic, CFSG or transitive-count input is used here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.LabelledTransitiveBlockCodeCardinality
open LabelledTransitiveBlockCode ActualFullWreathFamily

local instance subgroupFinite {G : Type} [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
local instance primitiveFintype (r : ℕ) : Fintype (Primitive r) := Fintype.ofFinite _
local instance transitiveFintype (t : ℕ) : Fintype (Transitive t) := Fintype.ofFinite _
local instance widthFintype (n : ℕ) : Fintype (Width n) := Fintype.ofFinite _

abbrev Cell (n : ℕ) (r t : Width n) :=
  Σ R : Primitive r.val.val,Σ Q : Transitive t.val.val,
    (Fin n ≃ Fin r.val.val × Fin t.val.val) × Family R.val Q.val (Fin t.val.val)

theorem chart_card_eq_factorial (n r t : ℕ) (hprod : r*t=n) :
    Nat.card (Fin n ≃ Fin r × Fin t) = n.factorial := by
  let e : Fin n ≃ Fin r × Fin t := Fintype.equivOfCardEq (by
    simpa only [Fintype.card_fin,Fintype.card_prod] using hprod.symm)
  rw [Nat.card_eq_fintype_card,Fintype.card_equiv e,Fintype.card_fin]

theorem chart_card_eq_zero (n r t : ℕ) (hprod : r*t ≠ n) :
    Nat.card (Fin n ≃ Fin r × Fin t) = 0 := by
  apply Nat.card_eq_zero.mpr
  refine Or.inl ⟨fun e => ?_⟩
  exact hprod (by simpa only [Nat.card_fin,Nat.card_prod] using (Nat.card_congr e).symm)

theorem width_card_le (n : ℕ) : Nat.card (Width n) ≤ n+1 := by
  simpa only [Nat.card_fin] using
    (Finite.card_subtype_le (fun r : Fin (n+1) => 2 ≤ r.val))

private theorem cell_card_le (n P B : ℕ)
    (hP : ∀ r : Width n,Nat.card (Primitive r.val.val) ≤ P)
    (hB : ∀ r t : Width n,r.val.val*t.val.val=n →
      ∀ R : Primitive r.val.val,∀ Q : Transitive t.val.val,
        Nat.card (Family R.val Q.val (Fin t.val.val)) ≤ B)
    (r t : Width n) :
    Nat.card (Cell n r t) ≤ P*n.factorial*B*
      (∑ k ∈ Finset.range (n/2+1),Nat.card (Transitive k)) := by
  by_cases hprod : r.val.val*t.val.val=n
  · have hchart := chart_card_eq_factorial n r.val.val t.val.val hprod
    have htwo : 2*t.val.val ≤ n :=
      (Nat.mul_le_mul_right t.val.val r.property).trans_eq hprod
    have hmem : t.val.val ∈ Finset.range (n/2+1) := Finset.mem_range.mpr (by omega)
    have htop : Nat.card (Transitive t.val.val) ≤
        ∑ k ∈ Finset.range (n/2+1),Nat.card (Transitive k) :=
      Finset.single_le_sum (s := Finset.range (n/2+1))
        (f := fun k => Nat.card (Transitive k)) (fun _ _ => Nat.zero_le _) hmem
    have hrow (R : Primitive r.val.val) :
        Nat.card (Σ Q : Transitive t.val.val,
          (Fin n ≃ Fin r.val.val × Fin t.val.val) × Family R.val Q.val (Fin t.val.val)) ≤
          Nat.card (Transitive t.val.val)*(n.factorial*B) := by
      rw [Nat.card_sigma]
      calc
        _ ≤ ∑ _Q : Transitive t.val.val,n.factorial*B := by
          apply Finset.sum_le_sum
          intro Q _
          rw [Nat.card_prod,hchart]
          exact Nat.mul_le_mul_left _ (hB r t hprod R Q)
        _ = _ := by
          simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id]
    change Nat.card (Σ R : Primitive r.val.val,Σ Q : Transitive t.val.val,
      (Fin n ≃ Fin r.val.val × Fin t.val.val) × Family R.val Q.val (Fin t.val.val)) ≤ _
    rw [Nat.card_sigma]
    calc
      _ ≤ ∑ _R : Primitive r.val.val,Nat.card (Transitive t.val.val)*(n.factorial*B) :=
        Finset.sum_le_sum (fun R _ => hrow R)
      _ = Nat.card (Primitive r.val.val)*(Nat.card (Transitive t.val.val)*(n.factorial*B)) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id]
      _ ≤ P*((∑ k ∈ Finset.range (n/2+1),Nat.card (Transitive k))*(n.factorial*B)) :=
        Nat.mul_le_mul (hP r) (Nat.mul_le_mul_right _ htop)
      _ = _ := by ring
  · have hchart := chart_card_eq_zero n r.val.val t.val.val hprod
    change Nat.card (Σ R : Primitive r.val.val,Σ Q : Transitive t.val.val,
      (Fin n ≃ Fin r.val.val × Fin t.val.val) × Family R.val Q.val (Fin t.val.val)) ≤ _
    simp only [Nat.card_sigma,Nat.card_prod,hchart,zero_mul,Finset.sum_const_zero]
    exact Nat.zero_le _

theorem card_blockCode_le (n P B : ℕ)
    (hP : ∀ r : Width n,Nat.card (Primitive r.val.val) ≤ P)
    (hB : ∀ r t : Width n,r.val.val*t.val.val=n →
      ∀ R : Primitive r.val.val,∀ Q : Transitive t.val.val,
        Nat.card (Family R.val Q.val (Fin t.val.val)) ≤ B) :
    Nat.card (BlockCode n) ≤ (n+1)^2*P*n.factorial*B*
      (∑ k ∈ Finset.range (n/2+1),Nat.card (Transitive k)) := by
  let S := ∑ k ∈ Finset.range (n/2+1),Nat.card (Transitive k)
  let C := P*n.factorial*B*S
  have hcell (r t : Width n) : Nat.card (Cell n r t) ≤ C := cell_card_le n P B hP hB r t
  have hrow (r : Width n) : Nat.card (Σ t : Width n,Cell n r t) ≤ Nat.card (Width n)*C := by
    rw [Nat.card_sigma]
    calc
      _ ≤ ∑ _t : Width n,C := Finset.sum_le_sum (fun t _ => hcell r t)
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id]
  change Nat.card (Σ r : Width n,Σ t : Width n,Cell n r t) ≤ _
  rw [Nat.card_sigma]
  calc
    _ ≤ ∑ _r : Width n,Nat.card (Width n)*C := Finset.sum_le_sum (fun r _ => hrow r)
    _ = Nat.card (Width n)*(Nat.card (Width n)*C) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id]
    _ ≤ (n+1)*((n+1)*C) := Nat.mul_le_mul (width_card_le n)
      (Nat.mul_le_mul_right C (width_card_le n))
    _ = _ := by dsimp only [C,S]; ring

end SymmetricSubgroupAsymptotics.LabelledTransitiveBlockCodeCardinality
