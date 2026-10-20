import SymmetricSubgroupAsymptotics.MarkedC4NilpotentProductReduction
import SymmetricSubgroupAsymptotics.MarkedC4OrbitCutoffFamilies
import SymmetricSubgroupAsymptotics.MarkedC4NilpotentCompressedCutoff

/-! The product field on the EXACT bounded nilpotent middle count of the
relative row. Both actual image orbit cutoffs are derived from the source. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.BoundedNilpotentProductReduction
open OrbitCutoffFamilies NilpotentPhysicalProductEncoding

abbrev BoundedTarget (C b : ℕ) := {z : Target b //
  OrbitCutoff C z.1.2.2.1 ∧ OrbitCutoff C z.1.2.2.2}
local instance {C b : ℕ} (K : NilpotentFamily C b) : Group.IsNilpotent K.1 := K.2.1

def targetCode {C b : ℕ} (hC : 1<C) (K : NilpotentFamily C b) : BoundedTarget C b :=
  ⟨NilpotentPhysicalProductEncoding.targetCode ⟨K.1,K.2.1⟩,
    NilpotentCompressedCutoff.binary_cutoff K.1 hC K.2.2,
    NilpotentCompressedCutoff.odd_cutoff K.1 hC K.2.2⟩

def code {C b : ℕ} (hC : 1<C) (K : NilpotentFamily C b) :
    BoundedTarget C b × PhysicalGridLabels.Code b :=
  (targetCode hC K,NilpotentOriginalLabels.code K.1)

private theorem code_injective {C b : ℕ} (hC : 1<C) :
    Function.Injective (code (b := b) hC) := by
  intro K L h
  have hp := congrArg (fun z : BoundedTarget C b × PhysicalGridLabels.Code b => z.1.1) h
  have hc := congrArg Prod.snd h
  have he : NilpotentPhysicalProductEncoding.code (⟨K.1,K.2.1⟩ : Source b)=
      NilpotentPhysicalProductEncoding.code (⟨L.1,L.2.1⟩ : Source b) := Prod.ext hp hc
  have hs := NilpotentPhysicalProductEncoding.code_injective b he
  exact Subtype.ext (congrArg (fun z : Source b => z.val) hs)

def encoding {C : ℕ} (hC : 1<C) (b : ℕ) :
    ProductEncoding (NilpotentFamily C b) (BoundedTarget C b) (PhysicalGridLabels.Code b)
      (fun K => K.1) (fun z => z.1.1.2.2.1) where
  code := code hC
  code_injective := code_injective hC
  hom_card K := NilpotentLabelledActions.hom_card_le_binary_range K.1

def targetCount (C b r : ℕ) : ℝ :=
  ∑ z : BoundedTarget C b,
    (Nat.card (z.1.1.2.2.1 →* Multiplicative (ZMod 4)) : ℝ)^r

def row {C : ℕ} (hC : 1<C) (b : ℕ) :
    ProductEncodingRow (nilpotentCount C) (targetCount C) NilpotentProductReduction.labelCost b where
  A := NilpotentFamily C b
  B := BoundedTarget C b
  C := PhysicalGridLabels.Code b
  fintypeA := inferInstance
  fintypeB := inferInstance
  fintypeC := inferInstance
  source K := K.1
  target z := z.1.1.2.2.1
  sourceGroup _ := inferInstance
  sourceFinite _ := inferInstance
  targetGroup _ := inferInstance
  targetFinite _ := inferInstance
  encoding := encoding hC b
  source_identity _ := rfl
  target_identity _ := rfl
  auxiliary_bound := NilpotentProductReduction.alphabet_bound b

/-- This product field's source count is definitionally the relative row's
bounded nilpotent target count, with no hidden multiplicity change. -/
def reduction {C : ℕ} (hC : 1<C) :
    PublishedProductReduction (nilpotentCount C) (targetCount C) where
  q := NilpotentProductReduction.labelCost
  q_subquadratic := NilpotentProductReduction.labelCost_subquadratic
  row := row hC
end SymmetricSubgroupAsymptotics.MarkedC4.BoundedNilpotentProductReduction
