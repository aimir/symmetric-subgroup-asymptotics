import SymmetricSubgroupAsymptotics.JointCapacityEffectiveEnvelope
import SymmetricSubgroupAsymptotics.BinaryCarrierStarEnvelope

/-! Pure scalar comparisons with the twelve displayed H16 rows.
The original row retains its literal order coordinate. Only the effective
polygon budget min(n,k+m) is compared with the displayed order coordinate.
These certificates assert no normal-subgroup coverage or counting bound.
The third star intermediate row has a separate numerical certificate. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierMasterEnvelopes

/-- The first twelve entries of the original displayed H16/X/J/P menu.
The conditional presentation keeps each scalar lookup small. -/
def h16 (i : Fin 12) : JointCapacityRow :=
  if i.val = 0 then ⟨0,0,0,0,1,6⟩ else
  if i.val = 1 then ⟨1,1,1,1,2,5⟩ else
  if i.val = 2 then ⟨1,2,1,1,4,4⟩ else
  if i.val = 3 then ⟨2,3,2,2,3,3⟩ else
  if i.val = 4 then ⟨2,4,2,2,4,2⟩ else
  if i.val = 5 then ⟨3,6,3,3,6,0⟩ else
  if i.val = 6 then ⟨4,6,4,4,5,0⟩ else
  if i.val = 7 then ⟨4,7,4,4,4,0⟩ else
  if i.val = 8 then ⟨4,8,4,4,3,0⟩ else
  if i.val = 9 then ⟨5,11,3,3,1,0⟩ else
  if i.val = 10 then ⟨5,11,4,4,0,0⟩ else
  ⟨6,12,3,3,0,0⟩

theorem h16_eq_displayed (i : Fin 12) :
    h16 i = BinaryCarrierStarEnvelope.displayedRows ⟨i.val, by omega⟩ := by
  fin_cases i <;> rfl

/-- The scalar formula for the above-derived row; in particular n=d+w. -/
def aboveRow (d s e w : ℕ) : JointCapacityRow :=
  ⟨max e w, d + w, e, e, (s - w : ℕ), 0⟩

def pairFourTarget (w : Fin 7) : Fin 12 :=
  if w.val ≤ 2 then 5 else if w.val = 3 then 7 else
  if w.val = 4 then 8 else if w.val = 5 then 9 else 11

def pairSixTarget (w : Fin 7) : Fin 12 :=
  if w.val = 0 then 5 else if w.val = 1 then 6 else
  if w.val = 2 then 7 else if w.val ≤ 4 then 8 else
  if w.val = 5 then 9 else 11

def starTarget (w : Fin 6) : Fin 12 :=
  if w.val = 0 then 6 else if w.val = 1 then 7 else
  if w.val ≤ 4 then 8 else 10

theorem above_pair_four (w : Fin 7) :
    (aboveRow 4 6 3 w.val).EffectivelyBoundedBy (h16 (pairFourTarget w)) := by
  fin_cases w <;> constructor <;> norm_num [aboveRow, pairFourTarget, h16]

theorem above_pair_six (w : Fin 7) :
    (aboveRow 6 6 3 w.val).EffectivelyBoundedBy (h16 (pairSixTarget w)) := by
  fin_cases w <;> constructor <;> norm_num [aboveRow, pairSixTarget, h16]

theorem above_star (w : Fin 6) :
    (aboveRow 6 5 4 w.val).EffectivelyBoundedBy (h16 (starTarget w)) := by
  fin_cases w <;> constructor <;> norm_num [aboveRow, starTarget, h16]

/-- A scalar crossing row. The unrestricted b retains the original order
entry; the effective comparison uses w+2 instead of bounding b+w. -/
def pairCrossingRow (b w : ℕ) : JointCapacityRow :=
  ⟨w, b + w, 2, 2, (3 - w : ℕ), 1⟩

theorem pair_crossing (b : ℕ) (w : Fin 2) :
    (pairCrossingRow b (w.val + 1)).EffectivelyBoundedBy (h16 4) := by
  fin_cases w <;> constructor <;> norm_num [pairCrossingRow, h16] <;> omega

theorem pair_crossing_of_bounds (b w : ℕ) (hw1 : 1 ≤ w) (hw2 : w ≤ 2) :
    (pairCrossingRow b w).EffectivelyBoundedBy (h16 4) := by
  have h := pair_crossing b (⟨w - 1, by omega⟩ : Fin 2)
  have hw : w - 1 + 1 = w := by omega
  simpa only [hw] using h

theorem pair_small_bottom :
    (⟨0,0,0,0,1,4⟩ : JointCapacityRow).EffectivelyBoundedBy (h16 0) := by
  constructor <;> norm_num [h16]

theorem pair_small_radical :
    (⟨1,1,1,0,3,3⟩ : JointCapacityRow).EffectivelyBoundedBy (h16 2) := by
  constructor <;> norm_num [h16]

theorem pair_intermediate_one :
    (⟨1,2,1,1,2,2⟩ : JointCapacityRow).EffectivelyBoundedBy (h16 2) := by
  constructor <;> norm_num [h16]

theorem pair_intermediate_two :
    (⟨2,3,2,1,3,1⟩ : JointCapacityRow).EffectivelyBoundedBy (h16 3) := by
  constructor <;> norm_num [h16]

theorem large_pair_small_bottom :
    (⟨0,0,0,0,1,6⟩ : JointCapacityRow).EffectivelyBoundedBy (h16 0) := by
  constructor <;> norm_num [h16]

theorem large_pair_small_one :
    (⟨1,1,1,0,2,5⟩ : JointCapacityRow).EffectivelyBoundedBy (h16 1) := by
  constructor <;> norm_num [h16]

theorem large_pair_small_two :
    (⟨1,2,1,1,1,4⟩ : JointCapacityRow).EffectivelyBoundedBy (h16 2) := by
  constructor <;> norm_num [h16]

theorem large_pair_small_radical :
    (⟨2,3,2,1,3,3⟩ : JointCapacityRow).EffectivelyBoundedBy (h16 3) := by
  constructor <;> norm_num [h16]

theorem large_pair_intermediate_one :
    (⟨1,4,2,2,2,2⟩ : JointCapacityRow).EffectivelyBoundedBy (h16 4) := by
  constructor <;> norm_num [h16]

theorem large_pair_intermediate_two :
    (⟨2,5,2,2,3,1⟩ : JointCapacityRow).EffectivelyBoundedBy (h16 4) := by
  constructor <;> norm_num [h16]

theorem star_small_bottom :
    (⟨0,0,0,0,1,6⟩ : JointCapacityRow).EffectivelyBoundedBy (h16 0) :=
  large_pair_small_bottom

theorem star_small_one :
    (⟨1,1,1,0,1,5⟩ : JointCapacityRow).EffectivelyBoundedBy (h16 1) := by
  constructor <;> norm_num [h16]

theorem star_small_radical :
    (⟨1,2,1,1,4,4⟩ : JointCapacityRow).EffectivelyBoundedBy (h16 2) := by
  constructor <;> norm_num [h16]

theorem star_intermediate_one :
    (⟨1,3,1,1,4,3⟩ : JointCapacityRow).EffectivelyBoundedBy (h16 2) := by
  constructor <;> norm_num [h16]

theorem star_intermediate_two :
    (⟨2,4,2,1,4,2⟩ : JointCapacityRow).EffectivelyBoundedBy (h16 4) := by
  constructor <;> norm_num [h16]

end SymmetricSubgroupAsymptotics.BinaryCarrierMasterEnvelopes
