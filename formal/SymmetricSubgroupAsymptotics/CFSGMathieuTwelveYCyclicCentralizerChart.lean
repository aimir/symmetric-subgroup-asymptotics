import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveWittCentralizerWhitelist
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finite.Perm
import Mathlib.Tactic.FinCases

/-! An actual ambient centralizer chart for the SAME original M12 element y.
The four phase-zero points are0,1,2,6. Every chart map is a cycle permutation
and four cyclic phase shifts. Completeness follows from injectivity and the
already-proved ambient centralizer cardinal1944, not any M12 membership
converse. No whitelist entries or target centralizer bound are supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveYCyclicCentralizerChart
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open M12Certificates.WittDesign

private def coordinateForward (p : Fin 12) : Fin 4 × ZMod 3 :=
  match p.val with
  | 0 => (0,0) | 1 => (1,0) | 2 => (2,0) | 3 => (2,2)
  | 4 => (2,1) | 5 => (1,2) | 6 => (3,0) | 7 => (0,1)
  | 8 => (3,1) | 9 => (3,2) | 10 => (0,2) | _ => (1,1)

private def coordinateInverse (z : Fin 4 × ZMod 3) : Fin 12 :=
  match z.1.val,z.2.val with
  | 0,0 => 0 | 0,1 => 7 | 0,_ => 10
  | 1,0 => 1 | 1,1 => 11 | 1,_ => 5
  | 2,0 => 2 | 2,1 => 4 | 2,_ => 3
  | _,0 => 6 | _,1 => 8 | _,_ => 9

def coordinates : Fin 12 ≃ Fin 4 × ZMod 3 where
  toFun := coordinateForward
  invFun := coordinateInverse
  left_inv := by
    intro p
    fin_cases p <;> decide +kernel
  right_inv := by
    rintro ⟨b,t⟩
    fin_cases b <;> fin_cases t <;> decide +kernel

theorem coordinates_y (p : Fin 12) :
    coordinates (y.val p) = ((coordinates p).1,(coordinates p).2+1) := by
  rw [y_coe_eq]
  fin_cases p <;> decide +kernel

abbrev Code := Equiv.Perm (Fin 4) × (Fin 4 → ZMod 3)

def fiberPermutation (c : Code) : Equiv.Perm (Fin 4 × ZMod 3) where
  toFun z := (c.1 z.1,z.2+c.2 z.1)
  invFun z := (c.1.symm z.1,z.2-c.2 (c.1.symm z.1))
  left_inv := by
    rintro ⟨b,t⟩
    simp
  right_inv := by
    rintro ⟨b,t⟩
    simp

def chart (c : Code) : Perm12 :=
  coordinates.trans ((fiberPermutation c).trans coordinates.symm)

theorem chart_coordinate (c : Code) (p : Fin 12) :
    coordinates (chart c p) =
      (c.1 (coordinates p).1,(coordinates p).2+c.2 (coordinates p).1) := by
  simp [chart,fiberPermutation]

theorem chart_commutes (c : Code) : chart c * y.val = y.val * chart c := by
  apply Equiv.ext
  intro p
  simp only [Equiv.Perm.mul_apply]
  apply coordinates.injective
  simp only [chart_coordinate,coordinates_y,Prod.fst,Prod.snd]
  simp only [add_assoc,add_comm,add_left_comm]

theorem chart_injective : Function.Injective chart := by
  rintro ⟨b,d⟩ ⟨b',d'⟩ h
  have hzero (j : Fin 4) : (b j,d j) = (b' j,d' j) := by
    have hp := congrArg (fun g : Perm12 =>
      coordinates (g (coordinates.symm (j,0)))) h
    simpa only [chart_coordinate,Equiv.apply_symm_apply,Prod.fst,Prod.snd,zero_add]
      using hp
  apply Prod.ext
  · exact Equiv.ext fun j => congrArg Prod.fst (hzero j)
  · exact funext fun j => congrArg Prod.snd (hzero j)

def centralizerChart (c : Code) : Subgroup.centralizer ({y.val} : Set Perm12) :=
  ⟨chart c,Subgroup.mem_centralizer_singleton_iff.mpr (chart_commutes c)⟩

theorem code_card : Nat.card Code = 1944 := by
  change Nat.card (Equiv.Perm (Fin 4) × (Fin 4 → ZMod 3)) = 1944
  rw [Nat.card_prod,Nat.card_perm,Nat.card_fun,Nat.card_zmod]
  norm_num [Nat.card_fin,Nat.factorial]

theorem complete (z : Perm12) (hz : z*y.val = y.val*z) :
    ∃ c : Code, chart c = z := by
  have hinj : Function.Injective centralizerChart := by
    intro c d h
    exact chart_injective (congrArg Subtype.val h)
  have hcard : Nat.card Code =
      Nat.card (Subgroup.centralizer ({y.val} : Set Perm12)) :=
    code_card.trans CFSGMathieuTwelveWittCentralizerWhitelist.y_ambient_centralizer_card.symm
  have hbij := (Nat.bijective_iff_injective_and_card centralizerChart).mpr ⟨hinj,hcard⟩
  obtain ⟨c,hc⟩ := hbij.2 ⟨z,Subgroup.mem_centralizer_singleton_iff.mpr hz⟩
  exact ⟨c,congrArg Subtype.val hc⟩

theorem original_y_centralizer_card_le (accepted : Finset Code)
    (bad_block : ∀ c : Code, chart c*y.val = y.val*chart c → c ∉ accepted →
      ∃ k : Fin 132, blockMap (chart c) (wittBlockAt k) ∉ wittBlocks) :
    Nat.card (Subgroup.centralizer ({y} : Set M12)) ≤ accepted.card :=
  CFSGMathieuTwelveWittCentralizerWhitelist.original_centralizer_card_le_of_bad_blocks
    y chart complete accepted bad_block

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveYCyclicCentralizerChart
