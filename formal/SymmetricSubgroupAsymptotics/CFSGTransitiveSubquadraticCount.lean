import SymmetricSubgroupAsymptotics.CFSGPrimitiveSubquadraticCount
import SymmetricSubgroupAsymptotics.CFSGUniformPrimitiveWreathFamilyCount
import SymmetricSubgroupAsymptotics.LabelledTransitiveBlockCodeCardinality
import SymmetricSubgroupAsymptotics.LMMRectangularCountAssembly
import SymmetricSubgroupAsymptotics.Non2PreE7MenuMassAggregation

/-! The literal labelled transitive count from CFSG alone. The reversible
actual block cover, primitive census and independently bounded whole
wreath-family maxima supply the numerical half-degree recurrence.
No transitive-count, exact Tracey or model-count callback is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGTransitiveSubquadraticCount
open LabelledTransitiveBlockCode LabelledTransitiveBlockCodeCardinality
open CFSGUniformPrimitiveWreathFamilyCount LMMRectangularCountAssembly

local instance subgroupFinite {G : Type} [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
local instance labelledFintype (n : ℕ) : Fintype (LabelledTransitiveSubgroup n) := Fintype.ofFinite _

private theorem frame_factorial_budget (A n : ℕ) (hn : 2 ≤ n) :
    (n+1)^2*n.factorial^(A*(Nat.log 2 n+2)^2)*n.factorial ≤
      n.factorial^((A+2)*(Nat.log 2 n+2)^2) := by
  have hsquareN : n+1 ≤ n^2 := by
    have hh := Nat.mul_le_mul_right n hn
    nlinarith only [hn,hh]
  have hsucc : n+1 ≤ n.factorial^2 :=
    hsquareN.trans (Nat.pow_le_pow_left (Nat.self_le_factorial n) 2)
  have hpoly : (n+1)^2 ≤ n.factorial^4 := by
    calc
      _ ≤ (n.factorial^2)^2 := Nat.pow_le_pow_left hsucc 2
      _ = _ := by rw [←pow_mul]
  have hsquare : 4 ≤ (Nat.log 2 n+2)^2 := by
    have hh := Nat.pow_le_pow_left (show 2 ≤ Nat.log 2 n+2 by omega) 2
    simpa only [show (2 : ℕ)^2=4 by decide] using hh
  have hexp : 4+A*(Nat.log 2 n+2)^2+1 ≤ (A+2)*(Nat.log 2 n+2)^2 := by
    nlinarith only [hsquare]
  calc
    _ ≤ n.factorial^4*n.factorial^(A*(Nat.log 2 n+2)^2)*n.factorial :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hpoly)
    _ = n.factorial^(4+A*(Nat.log 2 n+2)^2+1) := by simp only [pow_add,pow_one]
    _ ≤ _ := Nat.pow_le_pow_right (Nat.factorial_pos n) hexp

theorem exists_actual_recurrence (hCFSG : CFSG.CFSGClassification) :
    ∃ A : ℕ,∀ n : ℕ,2 ≤ n → Nat.card (LabelledTransitiveSubgroup n) ≤
      nodeWeight A familyMaximum n *
        (1+∑ k ∈ Finset.range (n/2+1),Nat.card (LabelledTransitiveSubgroup k)) := by
  obtain ⟨A,hA⟩ := CFSGPrimitiveSubquadraticCount.exists_uniform_count_budget hCFSG
  refine ⟨A+2,?_⟩
  intro n hn
  let P := n.factorial^(A*(Nat.log 2 n+2)^2)
  let P' := n.factorial^((A+2)*(Nat.log 2 n+2)^2)
  let D := 1+∑ r ∈ Finset.range (n+1),degreeTerm familyMaximum n r
  let S := ∑ k ∈ Finset.range (n/2+1),Nat.card (LabelledTransitiveSubgroup k)
  have hP (r : Width n) : Nat.card (Primitive r.val.val) ≤ P := by
    have hrn : r.val.val ≤ n := by have hh := r.val.isLt; omega
    have hfac := Nat.factorial_le hrn
    have hlog : Nat.log 2 r.val.val ≤ Nat.log 2 n := Nat.log_mono_right hrn
    have hexp : A*(Nat.log 2 r.val.val+2)^2 ≤ A*(Nat.log 2 n+2)^2 :=
      Nat.mul_le_mul_left A (Nat.pow_le_pow_left (Nat.add_le_add_right hlog 2) 2)
    exact (hA r.val.val r.property).trans
      ((Nat.pow_le_pow_left hfac _).trans (Nat.pow_le_pow_right (Nat.factorial_pos n) hexp))
  have hB (r t : Width n) (hprod : r.val.val*t.val.val=n)
      (R : Primitive r.val.val) (Q : Transitive t.val.val) :
      Nat.card (ActualFullWreathFamily.Family R.val Q.val (Fin t.val.val)) ≤ D := by
    have hrpos : 0 < r.val.val := by have hh := r.property; omega
    have hdiv : n/r.val.val=t.val.val := by
      calc
        n/r.val.val = (r.val.val*t.val.val)/r.val.val :=
          congrArg (fun z : ℕ => z/r.val.val) hprod.symm
        _ = t.val.val := Nat.mul_div_cancel_left t.val.val hrpos
    have hcond : 2 ≤ r.val.val ∧ 2 ≤ n/r.val.val ∧
        r.val.val*(n/r.val.val)=n := by
      refine ⟨r.property,?_,?_⟩
      · simpa only [hdiv] using t.property
      · simpa only [hdiv] using hprod
    have hterm : degreeTerm familyMaximum n r.val.val = familyMaximum r.val.val t.val.val := by
      dsimp only [degreeTerm]
      exact (if_pos hcond).trans (congrArg (familyMaximum r.val.val) hdiv)
    have hsingle : familyMaximum r.val.val t.val.val ≤
        ∑ i ∈ Finset.range (n+1),degreeTerm familyMaximum n i := by
      have hh := Finset.single_le_sum (s := Finset.range (n+1))
        (f := degreeTerm familyMaximum n) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr r.val.isLt)
      simpa only [hterm] using hh
    exact (family_card_le_maximum R.val R.property Q.val Q.property).trans
      (hsingle.trans (by dsimp only [D]; omega))
  have hprimitive : Nat.card (Primitive n) ≤ P := hA n hn
  have hblocks := card_blockCode_le n P D hP hB
  have hcode := LabelledTransitiveBlockCode.card_transitive_le hn
  have hsource : Nat.card (LabelledTransitiveSubgroup n) ≤
      P+((n+1)^2*P*n.factorial*D)*S :=
    hcode.trans (Nat.add_le_add hprimitive hblocks)
  have hD : 1 ≤ D := by dsimp only [D]; omega
  have hprimPower : P ≤ P' := Nat.pow_le_pow_right (Nat.factorial_pos n)
    (Nat.mul_le_mul_right ((Nat.log 2 n+2)^2) (by omega : A ≤ A+2))
  have hprimWeight : P ≤ P'*D := hprimPower.trans
    (Nat.le_mul_of_pos_right P' (by omega : 0 < D))
  have hframe : (n+1)^2*P*n.factorial*D ≤ P'*D :=
    Nat.mul_le_mul_right D (frame_factorial_budget A n hn)
  calc
    Nat.card (LabelledTransitiveSubgroup n) ≤ P+((n+1)^2*P*n.factorial*D)*S := hsource
    _ ≤ P'*D+(P'*D)*S := Nat.add_le_add hprimWeight (Nat.mul_le_mul_right S hframe)
    _ = nodeWeight (A+2) familyMaximum n*(1+S) := by
      dsimp only [nodeWeight,P',D]
      ring

theorem labelled_transitive_subquadratic (hCFSG : CFSG.CFSGClassification) :
    SubquadraticMenuIndexCount LabelledTransitiveSubgroup := by
  obtain ⟨A,hA⟩ := exists_actual_recurrence hCFSG
  exact subquadratic_of_labelled_cover A familyMaximum (familyMaximum_uniform hCFSG) hA

theorem transitiveCountInput_proved (hCFSG : CFSG.CFSGClassification) :
    LucchiniMenegazzoMorigiTransitiveCountInput := labelled_transitive_subquadratic hCFSG

end SymmetricSubgroupAsymptotics.CFSGTransitiveSubquadraticCount
