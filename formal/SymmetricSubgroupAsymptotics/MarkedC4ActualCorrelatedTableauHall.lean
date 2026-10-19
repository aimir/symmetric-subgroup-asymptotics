import SymmetricSubgroupAsymptotics.MarkedC4ActualTableauDensityEntropy
import SymmetricSubgroupAsymptotics.MarkedC4ActualCaseIColumnBridge
import SymmetricSubgroupAsymptotics.MarkedC4ActualLogPeelingAndSelfCost
import SymmetricSubgroupAsymptotics.MarkedC4ActualHallColumnCompression

/-! Actual fixed-tableau Case-I source enumeration and its correlated Hall
sum. Every Hall source is an actual subgroup from the SAME tableau family.
Only local physical density/nonexcess conditions are premises; no moment,
source-column capacity, enumeration or encoding bound is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualCorrelatedTableauHall
open ActualSubdirectFiltration ActualEfficientRowIncidence ActualSubdirectColumnProducts
open ActualTableauRowIncidence ActualTableauDensityEntropy ActualCaseIColumnBridge

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (D : ∀ i,Subgroup (F i)) (T : ∀ i j : Fin t,Subgroup (F j))
local instance : Fintype (TableauFamily F D T) := Fintype.ofFinite _

def offDiagonal (c n : ℕ → ℝ) : ℝ :=
  ∑ i : Fin t,(∑ j ∈ earlier i,(c i.val-c j.val)*n j.val)*(normalGen (D i) : ℝ)

private theorem sum_earlier_eq_range (f : ℕ → ℝ) (i : Fin t) :
    (∑ j ∈ earlier i,f j.val)=∑ j ∈ Finset.range i.val,f j := by
  apply Finset.sum_bij (fun j _ => j.val)
  · intro j hj
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
  · intro j hj k hk h
    exact Fin.ext h
  · intro m hm
    have hmi := Finset.mem_range.mp hm
    exact ⟨⟨m,hmi.trans i.isLt⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hmi⟩,rfl⟩
  · intro j hj
    rfl

theorem offDiagonal_eq_actual (H : TableauFamily F D T) (c n : ℕ → ℝ) :
    offDiagonal F D c n=
      ∑ m ∈ Finset.range t,∑ j ∈ Finset.range m,
        (c m-c j)*n j*(rankAt F H.val.val m : ℝ) := by
  unfold offDiagonal
  apply Finset.sum_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_range.mpr i.isLt
  · intro i hi j hj he
    exact Fin.ext he
  · intro m hm
    exact ⟨⟨m,Finset.mem_range.mp hm⟩,Finset.mem_univ _,rfl⟩
  · intro i hi
    have hd : rankAt F H.val.val i.val=normalGen (D i) := by
      simp only [rankAt,dif_pos i.isLt,H.val.property.2.2 i]
    rw [hd,← Finset.sum_mul]
    exact congrArg (fun z : ℝ => z*(normalGen (D i) : ℝ))
      (sum_earlier_eq_range (fun j : ℕ => (c i.val-c j)*n j) i)

/-- The actual source columns remain coupled to the same normal ranks
and log-order packet, before a single Hall source is summed. -/
theorem offDiagonal_add_actualHall_le (H : TableauFamily F D T) (c n : ℕ → ℝ)
    {a r : ℝ} (ha : 0≤a) (hr : 0≤r)
    (hn : ∀ m<t,0≤n m) (hc0 : ∀ m<t,0≤c m) (hc1 : ∀ m<t,c m≤1)
    (hmono : ∀ j m,j≤m → m<t → c j≤c m)
    (hclog : ∀ i : Fin t,(Nat.clog 2 (Nat.card (D i)) : ℝ)=c i.val*n i.val)
    (hnonexcess : ∀ i : Fin t,(normalGen (D i) : ℝ)≤n i.val/4) :
    offDiagonal F D c n+
      psi (a/2+r) (col (Abelianization H.val.val) 0)+
      psi r (col (Abelianization H.val.val) 1)≤markedF (a+prefixWeight n t) r := by
  rw [offDiagonal_eq_actual F D T H]
  apply entropy_add_actualHall_le F H.val.val H.val.property.1 n c ha hr hn hc0 hc1 hmono
  · intro m hm
    simpa only [layerOrder,dif_pos hm,H.val.property.2.2 ⟨m,hm⟩] using hclog ⟨m,hm⟩
  · intro m hm
    simpa only [rankAt,dif_pos hm,H.val.property.2.2 ⟨m,hm⟩] using hnonexcess ⟨m,hm⟩

/-- The actual source-family cardinality pays precisely off-diagonal
entropy plus the linear diagonal cost of bounded physical factors. -/
theorem card_le_offDiagonal_selfCost (H : TableauFamily F D T) (c n : ℕ → ℝ) {B : ℝ}
    (hentry : ∀ i j : Fin t,j.val ≤ i.val →
      Real.logb 2 (Nat.card (T i j))≤c i.val*n j.val)
    (hdiag : ∀ i : Fin t,Real.logb 2 (Nat.card (D i))=c i.val*n i.val)
    (hF : ∀ i : Fin t,Real.logb 2 (Nat.card (F i))≤B) :
    (Nat.card (TableauFamily F D T) : ℝ)≤
      (2 : ℝ)^(offDiagonal F D c n+(t : ℝ)*B^2) := by
  letI (i : Fin t) : (D i).Normal := by
    rw [← H.val.property.2.2 i]
    exact diagonalNormal F H.val.val H.val.property.1 i
  have hs := ActualLogPeelingAndSelfCost.total_diagonal_self_cost_le F D hF
  have hc := card_le_density_entropy F D T H (fun i => c i.val) (fun i => n i.val)
    hentry hdiag
  apply hc.trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
  simp only [add_mul,Finset.sum_add_distrib]
  unfold offDiagonal
  have hdiagSum : (∑ i : Fin t,c i.val*n i.val*(normalGen (D i) : ℝ))≤(t : ℝ)*B^2 := by
    simpa only [hdiag,Fintype.card_fin] using hs
  linarith

/-- The SAME actual tableau family and its actual first two source
columns are summed. The single C4^r group occurs only in the Hall target. -/
theorem fullSecond_sum_le (H : TableauFamily F D T)
    (c n : ℕ → ℝ) (m r : ℕ) (A : Type) [CommGroup A] [Finite A]
    (hA : HasExp2 A (2+m)) {a B : ℝ} (ha : 0≤a)
    (hcard : (Nat.card A : ℝ)≤(2 : ℝ)^(a/2))
    (hn : ∀ k<t,0≤n k) (hc0 : ∀ k<t,0≤c k) (hc1 : ∀ k<t,c k≤1)
    (hmono : ∀ j k,j≤k → k<t → c j≤c k)
    (hentry : ∀ i j : Fin t,j.val ≤ i.val →
      Real.logb 2 (Nat.card (T i j))≤c i.val*n j.val)
    (hdiag : ∀ i : Fin t,Real.logb 2 (Nat.card (D i))=c i.val*n i.val)
    (hclog : ∀ i : Fin t,(Nat.clog 2 (Nat.card (D i)) : ℝ)=c i.val*n i.val)
    (hnonexcess : ∀ i : Fin t,(normalGen (D i) : ℝ)≤n i.val/4)
    (hF : ∀ i : Fin t,Real.logb 2 (Nat.card (F i))≤B) :
    (∑ E : TableauFamily F D T,(Nat.card
      (AbelianProductGraphClassification.FullSecond
        (A × Multiplicative (Fin r → ZMod 4)) E.val.val) : ℝ)) ≤
      ((∏ k ∈ Finset.range (2+m),
        ((col (A × Multiplicative (Fin r → ZMod 4)) k : ℝ)+1))*4^(2+m))*
          (2 : ℝ)^(markedF (a+prefixWeight n t) r+(t : ℝ)*B^2) := by
  let Q : ℝ := (∏ k ∈ Finset.range (2+m),
    ((col (A × Multiplicative (Fin r → ZMod 4)) k : ℝ)+1))*4^(2+m)
  let Z : ℝ := markedF (a+prefixWeight n t) r-offDiagonal F D c n
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hE (E : TableauFamily F D T) :
      (Nat.card (AbelianProductGraphClassification.FullSecond
        (A × Multiplicative (Fin r → ZMod 4)) E.val.val) : ℝ)≤Q*(2 : ℝ)^Z := by
    letI : Fintype (Subgroup (A × Multiplicative (Fin r → ZMod 4))) := Fintype.ofFinite _
    have hh := ActualHallColumnCompression.fullSecond_le m r A hA E.val.val hcard
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ hQ
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
    have hp := offDiagonal_add_actualHall_le F D T E c n ha (Nat.cast_nonneg r)
      hn hc0 hc1 hmono hclog hnonexcess
    dsimp [Z]
    linarith
  calc
    _ ≤ ∑ _E : TableauFamily F D T,Q*(2 : ℝ)^Z :=
      Finset.sum_le_sum (fun E _ => hE E)
    _ = (Nat.card (TableauFamily F D T) : ℝ)*(Q*(2 : ℝ)^Z) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
    _ ≤ (2 : ℝ)^(offDiagonal F D c n+(t : ℝ)*B^2)*(Q*(2 : ℝ)^Z) :=
      mul_le_mul_of_nonneg_right
        (card_le_offDiagonal_selfCost F D T H c n hentry hdiag hF) (by positivity)
    _ = _ := by
      change (2 : ℝ)^(offDiagonal F D c n+(t : ℝ)*B^2)*(Q*(2 : ℝ)^Z)=
        Q*(2 : ℝ)^(markedF (a+prefixWeight n t) r+(t : ℝ)*B^2)
      calc
        _ = Q*((2 : ℝ)^(offDiagonal F D c n+(t : ℝ)*B^2)*(2 : ℝ)^Z) := by ring
        _ = Q*(2 : ℝ)^((offDiagonal F D c n+(t : ℝ)*B^2)+Z) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
        _ = _ := by dsimp [Z]; congr 1; ring

end SymmetricSubgroupAsymptotics.MarkedC4.ActualCorrelatedTableauHall
