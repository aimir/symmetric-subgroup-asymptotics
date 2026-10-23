import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalSignedRootAction
import SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyIndex
import Mathlib.Tactic.NormNum

/-! The actual signed simple-chart stabilizer has index at most two
inside the actual opposed-Sylow stabilizer. Its definitions assume
neither field action nor type preservation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalSimpleStabilizer
open CFSGGTwoD4GeckOriginalSignedRootAction CFSGGTwoD4GeckOriginalSimpleParameters
open CFSGGTwoD4GeckOriginalProjection CFSGGTwoD4GeckOriginalOppositeAlignment
open CFSGSubgroupFamilyStabilizer CFSGSubgroupFamilyIndex CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective CartanMatrix.G₂ K)]

def pairStabilizer : Subgroup (MulAut (Projective CartanMatrix.G₂ K)) :=
  familyStabilizer (fun neg : Bool => if neg then originalNegative K
    else (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K)))

def simpleStabilizer : Subgroup (pairStabilizer K p) :=
  (familyStabilizer (fun z : Bool × Bool => (originalSimpleHom K z.1 z.2).range)).subgroupOf
    (pairStabilizer K p)

def simpleStabilizerAction : simpleStabilizer K p →* MulAut (Projective CartanMatrix.G₂ K) :=
  (pairStabilizer K p).subtype.comp (simpleStabilizer K p).subtype

theorem pair_preserves_positive (f : pairStabilizer K p) :
    (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K)).map f.val.toMonoidHom =
      (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K)) := f.property false

theorem pair_preserves_negative (f : pairStabilizer K p) :
    (originalNegative K).map f.val.toMonoidHom = originalNegative K := f.property true

theorem simple_preserves_chart (f : simpleStabilizer K p) (neg a : Bool) :
    (originalSimpleHom K neg a).range.map (simpleStabilizerAction K p f).toMonoidHom =
      (originalSimpleHom K neg a).range := f.property (neg, a)

private def signedPermutation (sigma : Equiv.Perm Bool) : Equiv.Perm (Bool × Bool) :=
  Equiv.prodCongr (Equiv.refl Bool) sigma

theorem simple_stabilizer_index_le_two : (simpleStabilizer K p).index ≤ 2 := by
  classical
  let Allowed := {tau : Equiv.Perm (Bool × Bool) //
    ∃ sigma : Equiv.Perm Bool, signedPermutation sigma = tau}
  have hindex : (simpleStabilizer K p).index ≤ Nat.card Allowed := by
    apply family_index_le_permutations (pairStabilizer K p)
      (fun z : Bool × Bool => (originalSimpleHom K z.1 z.2).range)
      (fun tau => ∃ sigma : Equiv.Perm Bool, signedPermutation sigma = tau)
    intro f
    obtain ⟨sigma, hsigma⟩ := exists_original_signed_root_permutation K p f.val
      (pair_preserves_positive K p f) (pair_preserves_negative K p f)
    exact ⟨signedPermutation sigma, ⟨sigma, rfl⟩, fun z => hsigma z.1 z.2⟩
  have hcard : Nat.card Allowed ≤ Nat.card (Equiv.Perm Bool) := by
    let label : Equiv.Perm Bool → Allowed := fun sigma => ⟨signedPermutation sigma, ⟨sigma, rfl⟩⟩
    have hsurj : Function.Surjective label := by
      rintro ⟨tau, sigma, he⟩
      exact ⟨sigma, Subtype.ext he⟩
    exact Nat.card_le_card_of_surjective label hsurj
  have htwo : Nat.card (Equiv.Perm Bool) = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num
  exact (hindex.trans hcard).trans htwo.le

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalSimpleStabilizer
