import SymmetricSubgroupAsymptotics.RepeatedMarkerNormalizedProfile

/-!
# Complete natural support parameters for the positive-defect marker family

Original support triples and every compatible exterior multiplicity vector
are bounded by their actual degree. The complete finite boxes are therefore
exhaustive. A support triple together with its retained width maps injectively
to the actual positive-defect parameter fibre, without a profile-count factor.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.RepeatedMarkerPositiveParameters

open RepeatedMarkerAggregateProfile RepeatedMarkerNormalizedProfile MarkerGeometry

abbrev Support (N epsilon : ℕ) :=
  {s : Fin (2*N+epsilon+1) × Fin (2*N+epsilon+1) × Fin (2*N+epsilon+1) //
    totalDegree s.1.1 s.2.1.1 s.2.2.1 = 2*N+epsilon ∧
      1 ≤ (s.2.1.1+s.2.2.1-epsilon)/2}

namespace Support

def r {N epsilon : ℕ} (s : Support N epsilon) : ℕ := s.1.1.1
def g {N epsilon : ℕ} (s : Support N epsilon) : ℕ := s.1.2.1.1
def f {N epsilon : ℕ} (s : Support N epsilon) : ℕ := s.1.2.2.1

theorem balance {N epsilon : ℕ} (s : Support N epsilon) :
    totalDegree s.r s.g s.f = 2*N+epsilon := s.2.1

theorem positive {N epsilon : ℕ} (s : Support N epsilon) :
    1 ≤ (s.g+s.f-epsilon)/2 := s.2.2

theorem ext {N epsilon : ℕ} {s t : Support N epsilon}
    (hr : s.r = t.r) (hg : s.g = t.g) (hf : s.f = t.f) : s = t :=
  Subtype.ext (Prod.ext (Fin.ext hr) (Prod.ext (Fin.ext hg) (Fin.ext hf)))

/-- Every natural support solution is included; boundedness follows from
the actual nonnegative degree identity. -/
def ofNat (N epsilon r g f : ℕ) (hn : totalDegree r g f = 2*N+epsilon)
    (hD : 1 ≤ (g+f-epsilon)/2) : Support N epsilon :=
  ⟨(⟨r,by unfold totalDegree at hn; omega⟩,
    ⟨g,by unfold totalDegree at hn; omega⟩,
    ⟨f,by unfold totalDegree at hn; omega⟩),hn,hD⟩

end Support

abbrev Occurrence (N epsilon : ℕ) := Σ s : Support N epsilon, AdmissibleWidth s.g

local instance defectFibreFinite (N epsilon D : ℕ) : Finite (DefectFibre N epsilon D) :=
  Finite.of_injective profileCode profileCode_injective

local instance defectFibreFintype (N epsilon D : ℕ) : Fintype (DefectFibre N epsilon D) :=
  Fintype.ofFinite _

abbrev Entry (N epsilon : ℕ) := Σ D : Finset.Icc 1 N, DefectFibre N epsilon D.1

def parameterOfOccurrence (N epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (z : Occurrence N epsilon) : Parameters N epsilon :=
  parameter N epsilon z.1.r z.1.g z.1.f hepsilon z.1.balance z.2

def entry (N epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (z : Occurrence N epsilon) : Entry N epsilon :=
  let p := parameterOfOccurrence N epsilon hepsilon z
  ⟨⟨p.defect,Finset.mem_Icc.mpr ⟨z.1.positive,p.defect_le⟩⟩,p,rfl⟩

theorem entry_injective (N epsilon : ℕ) (hepsilon : epsilon ≤ 1) :
    Function.Injective (entry N epsilon hepsilon) := by
  rintro ⟨s,q⟩ ⟨t,q'⟩ h
  have hp := congrArg (fun e : Entry N epsilon => e.2.1) h
  have hg : s.g = t.g := congrArg Parameters.g hp
  have hf : s.f = t.f := congrArg Parameters.f hp
  have hq : q.1.1 = q'.1.1 := congrArg Parameters.q hp
  have hM : s.r+q.1.1 = t.r+q'.1.1 := congrArg Parameters.M hp
  have hr : s.r = t.r := by omega
  have hst : s = t := Support.ext hr hg hf
  subst t
  have hqq : q = q' := Subtype.ext (Fin.ext hq)
  subst q'
  rfl

/-- Any nonnegative weight on the complete actual positive-defect fibre
can be summed over original supports without an additional multiplicity. -/
theorem sum_occurrences_le (N epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (w : Parameters N epsilon → ℝ) (hw : ∀ p, 0 ≤ w p) :
    (∑ z : Occurrence N epsilon, w (parameterOfOccurrence N epsilon hepsilon z)) ≤
      ∑ D ∈ Finset.Icc 1 N, ∑ p : DefectFibre N epsilon D, w p.1 := by
  calc
    _ = ∑ e ∈ Finset.univ.image (entry N epsilon hepsilon), w e.2.1 := by
      rw [Finset.sum_image (fun _ _ _ _ h => entry_injective N epsilon hepsilon h)]
      rfl
    _ ≤ ∑ e : Entry N epsilon, w e.2.1 :=
      Finset.sum_le_univ_sum_of_nonneg (fun e => hw e.2.1)
    _ = _ := by
      rw [Fintype.sum_sigma (fun e : Entry N epsilon => w e.2.1)]
      exact Finset.sum_coe_sort (Finset.Icc 1 N)
        (fun D : ℕ => ∑ p : DefectFibre N epsilon D, w p.1)

variable {α : Type} [Fintype α] (Ω : α → Type)
    [∀ a, Fintype (Ω a)] [∀ a, Nonempty (Ω a)]

abbrev ProfileCode (r : ℕ) := Fin (2*r+1) × (α → Fin (2*r+1))

def decodeProfile {r : ℕ} (c : ProfileCode (α := α) r) : Profile (α := α) :=
  (c.1.1,fun a => (c.2 a).1)

/-- Every original multiplicity vector with the specified degree, not a
selected list of profile examples. -/
def profiles (r : ℕ) : Finset (Profile (α := α)) :=
  (Finset.univ.image (decodeProfile (α := α) (r := r))).filter
    (fun t => 2*t.1 + RepeatedMarkerMergedProfile.exteriorDegree Ω t.2 = 2*r)

theorem mem_profiles (r : ℕ) (t : Profile (α := α)) :
    t ∈ profiles Ω r ↔ 2*t.1 + RepeatedMarkerMergedProfile.exteriorDegree Ω t.2 = 2*r := by
  constructor
  · intro ht
    exact (Finset.mem_filter.mp ht).2
  · intro ht
    apply Finset.mem_filter.mpr
    refine ⟨?_,ht⟩
    have hp : t.1 < 2*r+1 := by omega
    have hm (a : α) : t.2 a < 2*r+1 := by
      have hpos : 1 ≤ Fintype.card (Ω a) := Nat.succ_le_of_lt Fintype.card_pos
      have hmul : t.2 a ≤ t.2 a * Fintype.card (Ω a) := by nlinarith
      have hsum : t.2 a * Fintype.card (Ω a) ≤ RepeatedMarkerMergedProfile.exteriorDegree Ω t.2 :=
        Finset.single_le_sum (f := fun b => t.2 b * Fintype.card (Ω b))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
      omega
    let c : ProfileCode (α := α) r := (⟨t.1,hp⟩,fun a => ⟨t.2 a,hm a⟩)
    exact Finset.mem_image.mpr ⟨c,Finset.mem_univ _,rfl⟩

theorem profiles_size (r : ℕ) :
    ∀ t ∈ profiles Ω r, 2*t.1 + RepeatedMarkerMergedProfile.exteriorDegree Ω t.2 = 2*r :=
  fun t ht => (mem_profiles Ω r t).mp ht

end SymmetricSubgroupAsymptotics.RepeatedMarkerPositiveParameters

end
