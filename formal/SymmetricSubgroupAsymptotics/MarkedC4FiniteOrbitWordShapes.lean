import SymmetricSubgroupAsymptotics.MarkedC4ActualBinaryOrbitWord

/-! A genuinely finite universal shape family for physical bounded words.
The actual orbit quotient is numbered, its positive degrees are retained,
and the original point bijection is constructed. No list of orbit types or
partition coverage is supplied as a premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.FiniteOrbitWordShapes

structure Shape (C b : ℕ) where
  length : Fin (b+1)
  degrees : Fin length.val → Fin C
  positive : ∀ i,0 < (degrees i).val
  total : ∑ i,(degrees i).val = b

def Shape.code {C b : ℕ} (S : Shape C b) :
    Σ t : Fin (b+1),Fin t.val → Fin C := ⟨S.length,S.degrees⟩

theorem Shape.code_injective {C b : ℕ} : Function.Injective (@Shape.code C b) := by
  intro S T h
  cases S
  cases T
  cases h
  rfl

instance {C b : ℕ} : Finite (Shape C b) :=
  Finite.of_injective Shape.code Shape.code_injective
instance {C b : ℕ} : Fintype (Shape C b) := Fintype.ofFinite _

abbrev Points {C b : ℕ} (S : Shape C b) := Σ i : Fin S.length.val,Fin (S.degrees i).val

theorem card_points {C b : ℕ} (S : Shape C b) : Fintype.card (Points S)=b := by
  simpa only [Fintype.card_sigma,Fintype.card_fin] using S.total

def canonicalPoints {C b : ℕ} (S : Shape C b) : Points S ≃ Fin b :=
  (Fintype.equivFin (Points S)).trans (finCongr (card_points S))

variable {b C : ℕ} (G : Subgroup (PermutationGroup b))
local instance : Fintype (ActualBinaryOrbitWord.Index G) := Fintype.ofFinite _

def length : ℕ := Fintype.card (ActualBinaryOrbitWord.Index G)
def number : ActualBinaryOrbitWord.Index G ≃ Fin (length G) := Fintype.equivFin _

theorem length_le : length G ≤ b := by
  have h := Nat.card_le_card_of_injective
    (fun i : ActualBinaryOrbitWord.Index G => i.out) Quotient.out_injective
  simpa only [length,Nat.card_eq_fintype_card,Fintype.card_fin] using h

def actualDegrees (hG : OrbitCutoffFamilies.OrbitCutoff C G) :
    Fin (length G) → Fin C := fun i =>
  ⟨ActualBinaryOrbitWord.degree G ((number G).symm i),
    ActualBinaryOrbitWord.degree_lt G hG ((number G).symm i)⟩

/-- Numbering the ACTUAL orbits constructs the physical finite word. -/
def originalCoordinates (hG : OrbitCutoffFamilies.OrbitCutoff C G) :
    Fin b ≃ Σ i : Fin (length G),Fin (actualDegrees G hG i).val :=
  (ActualBinaryOrbitWord.pointCoordinates G).trans
    (Equiv.sigmaCongrLeft' (number G))

def actualShape (hG : OrbitCutoffFamilies.OrbitCutoff C G) : Shape C b where
  length := ⟨length G,Nat.lt_succ_of_le (length_le G)⟩
  degrees := actualDegrees G hG
  positive i := ActualBinaryOrbitWord.positive_degree G ((number G).symm i)
  total := by
    have h := Fintype.card_congr (originalCoordinates G hG)
    simpa only [Fintype.card_fin,Fintype.card_sigma] using h.symm

/-- This is the actual original label bijection to the selected finite word. -/
def labels (hG : OrbitCutoffFamilies.OrbitCutoff C G) : Fin b ≃ Points (actualShape G hG) :=
  originalCoordinates G hG

/-- A SINGLE common finite alphabet suffices, even though word shapes vary.
The physical alphabet has exactly b! elements. -/
def labelCode (hG : OrbitCutoffFamilies.OrbitCutoff C G) : Equiv.Perm (Fin b) :=
  (labels G hG).trans (canonicalPoints (actualShape G hG))

theorem label_alphabet_card : Fintype.card (Equiv.Perm (Fin b))=b.factorial := by
  simp only [Fintype.card_perm,Fintype.card_fin]

end SymmetricSubgroupAsymptotics.MarkedC4.FiniteOrbitWordShapes
