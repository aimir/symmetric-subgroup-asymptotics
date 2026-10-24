import SymmetricSubgroupAsymptotics.CFSGFFourOriginalInitialCoefficientBlock
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalUpperCoefficientCertificates
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalRootFamilyParents

/-! Assembly of the complete sparse integral F4 coefficient certificate.
The mixed identities are transported from the checked small blocks by
finite agreement of their nonzero rows; no dense coefficient table or
new source expansion is used. The actual original-source action theorem
is installed separately through the shared family induction. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalFullCoefficientCertificate
open CFSGFFourOriginalRootFamilyProfile CFSGIntegralRootActionEntries
open CFSGFFourOriginalSimpleActionEntries CFSGFFourOriginalRootFamilyParents
local notation "A" => CartanMatrix.F₄

def raisingEntry (i:Fin 4) : Slot→Slot×ℤ
  | .inr b=>CFSGFFourOriginalInitialCoefficientBlock.raisingEntry i (.inr b)
  | .inl j=>if j.val<7 then CFSGFFourOriginalInitialCoefficientBlock.raisingEntry i (.inl j)
    else CFSGFFourOriginalHighCoefficientBlock.raisingEntry i (.inl j)

def loweringEntry (a:Fin 4) : Slot→Slot×ℤ
  | .inr b=>CFSGFFourOriginalInitialCoefficientBlock.loweringEntry a (.inr b)
  | .inl j=>if j.val<10 then CFSGFFourOriginalInitialCoefficientBlock.loweringEntry a (.inl j)
    else CFSGFFourOriginalHighCoefficientBlock.loweringEntry a (.inl j)

theorem cartan_entries : ∀i b:Fin 4,raisingEntry i (.inr b)=cartanRaise i b := by
  decide +kernel

theorem simple_entries : ∀a i:Fin 4,
    loweringEntry a (.inl (simpleIndex i))=simpleLower a i := by decide +kernel

theorem parent_entries : ∀t:Fin 20,raisingEntry (parentNode t) (.inl (parentIndex t))=
    (.inl (childIndex t),parentCoefficient t) := by decide +kernel

theorem lowering_height : ∀a j,0<height j→(loweringEntry a j).2≠0→
    height (loweringEntry a j).1+1=height j := by decide +kernel

theorem raising_height : ∀i j,0<height j→(raisingEntry i j).2≠0→
    height (raisingEntry i j).1=height j+1 := by decide +kernel

theorem raising_weight : ∀i a j,0<height j→(raisingEntry i j).2≠0→
    integerWeight a (raisingEntry i j).1=A a i+integerWeight a j := by decide +kernel

private def agreesAt (E F:Fin 4→Slot→Slot×ℤ) (j:Slot) : Prop :=
    (∀i,raisingEntry i j=E i j) ∧ (∀a,loweringEntry a j=F a j) ∧
    (∀i a,(F a j).2≠0→ raisingEntry i (F a j).1=E i (F a j).1) ∧
    (∀i a,(E i j).2≠0→ loweringEntry a (E i j).1=F a (E i j).1)

private theorem agreement_initial : ∀j:Fin 24,rootHeight j≤3→agreesAt
    CFSGFFourOriginalInitialCoefficientBlock.raisingEntry
    CFSGFFourOriginalInitialCoefficientBlock.loweringEntry (.inl j) := by
  unfold agreesAt
  decide +kernel

private theorem agreement_four : ∀j:Fin 24,rootHeight j=4→agreesAt
    CFSGFFourOriginalHeightFiveCoefficientBlock.raisingEntry
    CFSGFFourOriginalHeightFiveCoefficientBlock.loweringEntry (.inl j) := by
  unfold agreesAt
  decide +kernel

private theorem agreement_five : ∀j:Fin 24,rootHeight j=5→agreesAt
    CFSGFFourOriginalHeightSixCoefficientBlock.raisingEntry
    CFSGFFourOriginalHeightSixCoefficientBlock.loweringEntry (.inl j) := by
  unfold agreesAt
  decide +kernel

private theorem agreement_high : ∀j:Fin 24,6≤rootHeight j→agreesAt
    CFSGFFourOriginalHighCoefficientBlock.raisingEntry
    CFSGFFourOriginalHighCoefficientBlock.loweringEntry (.inl j) := by
  unfold agreesAt
  decide +kernel

private theorem mixed_of_agreement (E F:Fin 4→Slot→Slot×ℤ) (j:Slot)
    (ha:agreesAt E F j)
    (hc:∀i a:Fin 4,(if a=i then (-integerWeight a j) • Pi.single j 1 else 0)+
      (F a j).2 • integerRow (E i (F a j).1)=
      (E i j).2 • integerRow (F a (E i j).1)) :
    ∀i a:Fin 4,(if a=i then (-integerWeight a j) • Pi.single j 1 else 0)+
      (loweringEntry a j).2 • integerRow (raisingEntry i (loweringEntry a j).1)=
      (raisingEntry i j).2 • integerRow (loweringEntry a (raisingEntry i j).1) := by
  obtain ⟨hE,hF,hEF,hFE⟩:=ha
  intro i a
  rw [hE i,hF a]
  have hleft:(F a j).2 • integerRow (raisingEntry i (F a j).1)=
      (F a j).2 • integerRow (E i (F a j).1) := by
    by_cases hz:(F a j).2=0
    · simp only [hz,zero_smul]
    · rw [hEF i a hz]
  have hright:(E i j).2 • integerRow (loweringEntry a (E i j).1)=
      (E i j).2 • integerRow (F a (E i j).1) := by
    by_cases hz:(E i j).2=0
    · simp only [hz,zero_smul]
    · rw [hFE i a hz]
  rw [hleft,hright]
  exact hc i a

private theorem height_four_indices : ∀j:Fin 24,rootHeight j=4→j=10∨j=11∨j=12 := by
  decide +kernel

theorem mixed_entries (i a:Fin 4) (j:Slot) (hj:0<height j) :
    (if a=i then (-integerWeight a j) • Pi.single j 1 else 0)+
      (loweringEntry a j).2 • integerRow (raisingEntry i (loweringEntry a j).1)=
      (raisingEntry i j).2 • integerRow (loweringEntry a (raisingEntry i j).1) := by
  cases j with
  | inr b=>exact (by change 0<0 at hj;omega)
  | inl j=>
    change 0<rootHeight j at hj
    by_cases hlo:rootHeight j≤3
    · apply mixed_of_agreement _ _ _ (agreement_initial j hlo) _ i a
      rcases (show rootHeight j=1∨rootHeight j=2∨rootHeight j=3 by omega) with h|h|h
      · exact CFSGFFourOriginalInitialCoefficientBlock.mixed_at_height_one j h
      · exact CFSGFFourOriginalInitialCoefficientBlock.mixed_at_height_two j h
      · exact CFSGFFourOriginalInitialCoefficientBlock.mixed_at_height_three j h
    by_cases hfour:rootHeight j=4
    · apply mixed_of_agreement _ _ _ (agreement_four j hfour) _ i a
      rcases height_four_indices j hfour with rfl|rfl|rfl
      · exact CFSGFFourOriginalHeightFiveCoefficientBlock.mixed_ten
      · exact CFSGFFourOriginalHeightFiveCoefficientBlock.mixed_eleven
      · exact CFSGFFourOriginalHeightFiveCoefficientBlock.mixed_twelve
    by_cases hfive:rootHeight j=5
    · exact mixed_of_agreement _ _ _ (agreement_five j hfive)
        (CFSGFFourOriginalHeightSixCoefficientBlock.mixed_at_height_five j hfive) i a
    · have hhigh:6≤rootHeight j:=by omega
      apply mixed_of_agreement _ _ _ (agreement_high j hhigh) _ i a
      by_cases hsix:rootHeight j=6
      · exact CFSGFFourOriginalHighCoefficientBlock.mixed_at_height_six j hsix
      · exact CFSGFFourOriginalUpperCoefficientCertificates.mixed_at_upper_height j (by omega)

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalFullCoefficientCertificate
