import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveFiveTuplePackedCompletion
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveCycleSeedClassBounds

/-! A960-point-image chart for the original fixed-point-free involution.
Every chart value is an actual original M12 word, obtained by completing
five points. No ambient-preservation membership converse occurs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveFixedPointFreeInvolutionChart
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveFiveTupleCompletion CFSGMathieuTwelveFiveTuplePackedCompletion
open CFSGMathieuTwelveSharpFiveRigidity FinitePermutationCycleSeedAssignments

def sourceSeeds : Fin 3 → Fin 12 := ![0,1,2]

theorem source_separated : CycleSeparated originalC.val 2 sourceSeeds := by
  decide +kernel

def cyclePoint (seed : Fin 3 → Fin 12) (q : Fin 3 × Fin 2) : Fin 12 :=
  (originalC.val^q.2.val) (seed q.1)

theorem cyclePoint_injective (seed : Fin 3 → Fin 12)
    (hs : CycleSeparated originalC.val 2 seed) : Function.Injective (cyclePoint seed) := by
  have h0 (i j : Fin 3) (hne : i ≠ j) : seed i ≠ seed j := by
    simpa only [pow_zero,Equiv.Perm.one_apply] using hs.2.2 i j hne (0 : Fin 2)
  have h1 (i j : Fin 3) (hne : i ≠ j) : originalC.val (seed i) ≠ seed j := by
    simpa only [pow_one] using hs.2.2 i j hne (1 : Fin 2)
  have hm (i : Fin 3) : originalC.val (seed i) ≠ seed i := by
    simpa only [pow_one] using hs.2.1 i (1 : Fin 2) (by decide)
  rintro ⟨i,e⟩ ⟨j,f⟩ he
  have hij : i = j := by
    by_contra hne
    fin_cases e <;> fin_cases f
    · exact h0 i j hne (by simpa only [cyclePoint,pow_zero,Equiv.Perm.one_apply] using he)
    · exact h1 j i (Ne.symm hne) (by simpa only [cyclePoint,pow_zero,pow_one,Equiv.Perm.one_apply] using he.symm)
    · exact h1 i j hne (by simpa only [cyclePoint,pow_zero,pow_one,Equiv.Perm.one_apply] using he)
    · apply h0 i j hne
      apply originalC.val.injective
      simpa only [cyclePoint,pow_one] using he
  subst j
  have hef : e = f := by
    fin_cases e <;> fin_cases f
    · rfl
    · exact (hm i (by simpa only [cyclePoint,pow_zero,pow_one,Equiv.Perm.one_apply] using he.symm)).elim
    · exact (hm i (by simpa only [cyclePoint,pow_zero,pow_one,Equiv.Perm.one_apply] using he)).elim
    · rfl
  exact congrArg (fun z : Fin 2 => (i,z)) hef

def labels : Fin 5 ↪ Fin 3 × Fin 2 where
  toFun := ![(0,0),(0,1),(1,0),(1,1),(2,0)]
  inj' := by decide +kernel

def targetTuple (seed : Fin 3 → Fin 12) (hs : CycleSeparated originalC.val 2 seed) :
    Fin 5 ↪ Fin 12 := labels.trans ⟨cyclePoint seed,cyclePoint_injective seed hs⟩

theorem targetTuple_apply (seed : Fin 3 → Fin 12)
    (hs : CycleSeparated originalC.val 2 seed) (i : Fin 5) :
    targetTuple seed hs i = ![seed 0,originalC.val (seed 0),seed 1,originalC.val (seed 1),seed 2] i := by
  fin_cases i <;> rfl

def sourceTuple : Fin 5 ↪ Fin 12 := targetTuple sourceSeeds source_separated
def frame : M12 := complete sourceTuple
def chart (seed : Fin 3 → Fin 12) (hs : CycleSeparated originalC.val 2 seed) : M12 :=
  complete (targetTuple seed hs) * frame⁻¹

private theorem hom_mul_apply {G X : Type*} [Group G] (rho : G →* Equiv.Perm X)
    (g h : G) (p : X) : rho (g*h) p = rho g (rho h p) := by
  rw [rho.map_mul]
  rfl

theorem chart_points (seed : Fin 3 → Fin 12) (hs : CycleSeparated originalC.val 2 seed)
    (i : Fin 5) : (chart seed hs).val (sourceTuple i) = targetTuple seed hs i := by
  have hf : frame.val.symm (sourceTuple i) = standardBase i := by
    rw [←complete_points sourceTuple i]
    exact Equiv.symm_apply_apply _ _
  calc
    (chart seed hs).val (sourceTuple i) =
        (complete (targetTuple seed hs)).val (frame.val.symm (sourceTuple i)) :=
      hom_mul_apply M12Subgroup.subtype _ _ _
    _ = targetTuple seed hs i := by rw [hf,complete_points]

private theorem centralizer_commute (g : Subgroup.centralizer ({originalC} : Set M12)) :
    Commute g.val.val originalC.val := by
  change g.val.val * originalC.val = originalC.val * g.val.val
  simpa only [Subgroup.coe_mul] using
    congrArg (fun z : M12 => z.val) (Subgroup.mem_centralizer_singleton_iff.mp g.property)

def imageSeeds (g : Subgroup.centralizer ({originalC} : Set M12)) : Fin 3 → Fin 12 :=
  fun i => g.val.val (sourceSeeds i)

theorem imageSeeds_separated (g : Subgroup.centralizer ({originalC} : Set M12)) :
    CycleSeparated originalC.val 2 (imageSeeds g) :=
  maps_cycle_separated originalC.val g.val.val 2 (centralizer_commute g) sourceSeeds source_separated

theorem chart_eq_centralizer (g : Subgroup.centralizer ({originalC} : Set M12)) :
    chart (imageSeeds g) (imageSeeds_separated g) = g.val := by
  apply eq_of_agree_five sourceTuple
  intro i
  rw [chart_points]
  change (originalC.val^(labels i).2.val) (g.val.val (sourceSeeds (labels i).1)) =
    g.val.val ((originalC.val^(labels i).2.val) (sourceSeeds (labels i).1))
  exact (congrArg (fun z : Perm12 => z (sourceSeeds (labels i).1))
    ((centralizer_commute g).pow_right (labels i).2.val).eq).symm

def rawC : ℕ → ℕ
  | 0 => 11 | 1 => 10 | 2 => 5 | 3 => 7 | 4 => 8 | 5 => 2
  | 6 => 9 | 7 => 3 | 8 => 4 | 9 => 6 | 10 => 1 | _ => 0

theorem rawC_eq (p : Fin 12) : rawC p.val = (originalC.val p).val := by
  fin_cases p <;> decide +kernel

def rawFrameInverse (p : ℕ) : ℕ := rawCompleteInverse 0 11 1 10 2 p

theorem rawFrameInverse_eq (p : Fin 12) : rawFrameInverse p.val = (frame.val.symm p).val := by
  have h := rawCompleteInverse_eq sourceTuple p
  change rawCompleteInverse 0 11 1 10 2 p.val = (frame.val.symm p).val at h
  exact h

def rawChart (a b c p : ℕ) : ℕ :=
  rawComplete a (rawC a) b (rawC b) c (rawFrameInverse p)

theorem rawChart_eq (seed : Fin 3 → Fin 12) (hs : CycleSeparated originalC.val 2 seed)
    (p : Fin 12) : rawChart (seed 0).val (seed 1).val (seed 2).val p.val =
      ((chart seed hs).val p).val := by
  have h := rawComplete_eq (targetTuple seed hs) (frame.val.symm p)
  simp only [targetTuple_apply] at h
  change rawComplete (seed 0).val (originalC.val (seed 0)).val (seed 1).val
    (originalC.val (seed 1)).val (seed 2).val (frame.val.symm p).val =
      ((complete (targetTuple seed hs)).val (frame.val.symm p)).val at h
  rw [←rawC_eq (seed 0),←rawC_eq (seed 1),←rawFrameInverse_eq p] at h
  calc
    rawChart (seed 0).val (seed 1).val (seed 2).val p.val =
        ((complete (targetTuple seed hs)).val (frame.val.symm p)).val := h
    _ = ((chart seed hs).val p).val := by
      exact congrArg Fin.val (hom_mul_apply M12Subgroup.subtype
        (complete (targetTuple seed hs)) frame⁻¹ p).symm

theorem originalC_cycleType : originalC.val.cycleType = Multiset.replicate 6 2 := by
  decide +kernel

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveFixedPointFreeInvolutionChart
