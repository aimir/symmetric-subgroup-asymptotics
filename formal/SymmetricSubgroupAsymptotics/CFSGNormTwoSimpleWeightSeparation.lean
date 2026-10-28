import SymmetricSubgroupAsymptotics.CFSGNormTwoOriginalSourceBaseActions
import SymmetricSubgroupAsymptotics.CFSGIntegralNormTwoSigns

/-! Actual norm-two lattice geometry behind the finite source-action
support conditions. Simple Cartan weights separate all integer labels;
raising cannot leave the positive cone, and a non-simple positive root
can lower to a root only inside that cone. No action table is an input. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoSimpleWeightSeparation
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGNormTwoOriginalPositiveSources CFSGNormTwoOriginalSourceBaseActions
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (hd : ∀i,A i i=2) (hs : A.transpose=A)
    (hp : (rationalMatrix A).PosDef)

include hs hp in
/-- Literal simple Cartan pairings separate integer coordinate labels. -/
theorem label_eq_of_simple_pairings (x y : Fin r→ℤ)
    (h : ∀a,integerPairing A (Pi.single a 1) x=
      integerPairing A (Pi.single a 1) y) : x=y := by
  have hz : ∀a,integerPairing A (x-y) (Pi.single a 1)=0 := by
    intro a
    rw [integer_symmetric A hs, map_sub, h, sub_self]
  have hn : integerPairing A (x-y) (x-y)=0 := by
    rw [CFSGIntegerPairingPositiveDescent.norm_coordinate_sum]
    simp only [hz,mul_zero,Finset.sum_const_zero]
  exact sub_eq_zero.mp ((norm_eq_zero_iff A hp _).mp hn)

include hs hp in
/-- The rational shifted-weight relation is an actual lattice-label sum. -/
theorem label_eq_add_simple (i : Fin r) (x y : Fin r→ℤ)
    (h : ∀a,(integerPairing A (Pi.single a 1) y:ℚ)=
      (A a i:ℚ)+(integerPairing A (Pi.single a 1) x:ℚ)) :
    y=x+Pi.single i 1 := by
  apply label_eq_of_simple_pairings A hs hp
  intro a
  have he : integerPairing A (Pi.single a 1) (Pi.single i 1)=A a i := by
    simp only [integerPairing,Matrix.toBilin'_single]
  rw [map_add,he]
  have ha : integerPairing A (Pi.single a 1) y=
      A a i+integerPairing A (Pi.single a 1) x := by
    exact_mod_cast h a
  omega

include hs hp in
/-- The rational lowering-weight relation is an actual lattice difference. -/
theorem label_eq_sub_simple (i : Fin r) (x y : Fin r→ℤ)
    (h : ∀a,(integerPairing A (Pi.single a 1) y:ℚ)=
      -(A a i:ℚ)+(integerPairing A (Pi.single a 1) x:ℚ)) :
    y=x-Pi.single i 1 := by
  apply label_eq_of_simple_pairings A hs hp
  intro a
  have he : integerPairing A (Pi.single a 1) (Pi.single i 1)=A a i := by
    simp only [integerPairing,Matrix.toBilin'_single]
  rw [map_sub,he]
  have ha : integerPairing A (Pi.single a 1) y=
      -A a i+integerPairing A (Pi.single a 1) x := by
    exact_mod_cast h a
  omega

/-- A genuine raising label is positive, independently of whether a root
with that label exists. -/
theorem raised_nonnegative (i : Fin r) (k : Positive A) :
    ∀a,0≤(k.val.val+Pi.single i 1 : Fin r→ℤ) a := by
  intro a
  apply add_nonneg (k.property a)
  simp only [Pi.single_apply]
  split_ifs <;> norm_num

include hd hs hp in
/-- If lowering a positive root of height greater than one gives another
root, the output root is positive. The exceptional simple-to-Cartan row
is handled by the ORIGINAL mixed Serre relation. -/
theorem lowered_root_nonnegative
    (ho : ∀i j,i≠j→A i j≤0) (i : Fin r) (k : Positive A)
    (hk : 1<rootHeight A k) (q : Roots A)
    (hq : q.val=k.val.val-Pi.single i 1) : ∀a,0≤q.val a := by
  rcases CFSGIntegralNormTwoSigns.norm_two_coordinates_one_sign A hs hp
    (fun a=>by rw [hd a];exact even_two) ho q.val q.property with hpos|hneg
  · exact hpos
  · have hbound : ∀a,k.val.val a≤(Pi.single i (1:ℤ) : Fin r→ℤ) a := by
      intro a
      have ha := hneg a
      rw [hq] at ha
      change k.val.val a-(Pi.single i (1:ℤ) : Fin r→ℤ) a≤0 at ha
      omega
    have hsum : (∑a,k.val.val a)≤1 := by
      calc
        _≤∑a,(Pi.single i (1:ℤ) : Fin r→ℤ) a :=
          Finset.sum_le_sum (fun a _=>hbound a)
        _=1 := by simp
    have hsum0 : 0≤∑a,k.val.val a := Finset.sum_nonneg (fun a _=>k.property a)
    have hh : rootHeight A k≤1 := by
      change (∑a,k.val.val a).toNat≤1
      omega
    omega

/-- Exact natural height shift for a positive raised root. -/
theorem raised_height (i : Fin r) (k q : Positive A)
    (hq : q.val.val=k.val.val+Pi.single i 1) :
    rootHeight A q=rootHeight A k+1 := by
  have hs0 : 0≤∑a,k.val.val a := Finset.sum_nonneg (fun a _=>k.property a)
  have he : (∑a,q.val.val a)=(∑a,k.val.val a)+1 := by
    simp only [hq,Pi.add_apply,Finset.sum_add_distrib]
    simp
  change (∑a,q.val.val a).toNat=(∑a,k.val.val a).toNat+1
  omega

/-- Exact natural height shift for a positive lowered root. -/
theorem lowered_height (i : Fin r) (k q : Positive A)
    (hq : q.val.val=k.val.val-Pi.single i 1) :
    rootHeight A q+1=rootHeight A k := by
  have hq0 : 0≤∑a,q.val.val a := Finset.sum_nonneg (fun a _=>q.property a)
  have he : (∑a,q.val.val a)=(∑a,k.val.val a)-1 := by
    simp only [hq,Pi.sub_apply,Finset.sum_sub_distrib]
    simp
  change (∑a,q.val.val a).toNat+1=(∑a,k.val.val a).toNat
  omega

end SymmetricSubgroupAsymptotics.CFSGNormTwoSimpleWeightSeparation
