import SymmetricSubgroupAsymptotics.CFSGNormTwoOriginalPositiveSources

/-! The ACTUAL original Cartan/positive/negative source family, containing
all original generators. Positive-weight comparison is proved from the
literal positive-definite integer pairing, uniformly for ADE. Neither
source spanning nor the source stability table is assumed or asserted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoOriginalSourceFamily
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGIntegerMatrixPairing
open CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGIntegerPairingPositiveDescent CFSGNormTwoOriginalPositiveSources
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (hd : ∀i,A i i=2) (hs : A.transpose=A)
    (hp : (rationalMatrix A).PosDef)

abbrev BasisIndex := Fin r ⊕ (Bool×Positive A)

include hd hs hp in
def vector : BasisIndex A→integralLattice A
  | .inl i=>latticeGenerator A (.H i)
  | .inr (neg,k)=>source A hd hs hp neg k

theorem generators_mem (g : CartanMatrix.Generators (Fin r)) :
    latticeGenerator A g∈Submodule.span ℤ (Set.range (vector A hd hs hp)) := by
  apply Submodule.subset_span
  cases g with
  | H i => exact ⟨.inl i,rfl⟩
  | E i =>
    refine ⟨.inr (false,simpleRoot A hd i),?_⟩
    exact source_simple A hd hs hp false i
  | F i =>
    refine ⟨.inr (true,simpleRoot A hd i),?_⟩
    exact source_simple A hd hs hp true i

include hs hp in
/-- Every simple raising weight plus a positive root weight has a positive
Cartan comparison direction, including the case where their sum is NOT a
root. This is precisely the positivity input to original-source lowering
induction, proved without a target representation or root list. -/
theorem positive_comparison (i : Fin r) (k : Positive A) :
    ∃a,0<(A a i:ℚ)+weight A a k := by
  let v : Fin r→ℤ:=k.val.val+Pi.single i 1
  have hv : ∀j,0≤v j := by
    intro j
    change 0≤k.val.val j+(Pi.single i (1:ℤ) : Fin r→ℤ) j
    apply add_nonneg (k.property j)
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  have hvne : v≠0 := by
    intro hz
    have hi := congrFun hz i
    change k.val.val i+(Pi.single i (1:ℤ) : Fin r→ℤ) i=0 at hi
    simp only [Pi.single_eq_same] at hi
    have hk := k.property i
    omega
  have hn : 0 < integerPairing A v v := by
    have hnonneg := norm_nonneg A hp v
    have hne : integerPairing A v v≠0 :=
      fun he=>hvne ((norm_eq_zero_iff A hp v).mp he)
    omega
  obtain ⟨a,_,ha⟩ := exists_positive_coordinate_pairing (integerPairing A) v hv hn
  have hsym : integerPairing A (Pi.single a 1) v=
      integerPairing A v (Pi.single a 1) := integer_symmetric A hs _ _
  have hpos : 0<(integerPairing A (Pi.single a 1) v:ℚ) := by
    rw [hsym]
    exact_mod_cast ha
  have he : (integerPairing A (Pi.single a 1) v:ℚ)=
      (A a i:ℚ)+weight A a k := by
    change (integerPairing A (Pi.single a 1) (k.val.val+Pi.single i 1):ℚ)=
      (A a i:ℚ)+(integerPairing A (Pi.single a 1) k.val.val:ℚ)
    rw [map_add,Int.cast_add]
    have hei : integerPairing A (Pi.single a 1) (Pi.single i 1)=A a i := by
      simp only [integerPairing,Matrix.toBilin'_single]
    rw [hei,add_comm]
  exact ⟨a,he ▸ hpos⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoOriginalSourceFamily
