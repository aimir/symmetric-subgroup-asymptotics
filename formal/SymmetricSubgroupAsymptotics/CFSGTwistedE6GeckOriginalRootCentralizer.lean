import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRootFamily
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! Actual matrix centralizers inside the semilinear fixed upper subgroup
map into the corresponding centralizers in the ORIGINAL projective group.
This retains full matrix root-line centralization as a sufficient condition;
it does not require the original projection to be faithful on all of J. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRootCentralizer
open CFSGTwistedE6GeckOriginalRootFamily CFSGTwistedE6GeckFixedPositiveProjection
open CFSGTwistedE6GeckOriginalProjection CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckFixedRootFamilyCover CFSGSerreOrdinaryTwists
open CFSGNormTwoRootPairing

private theorem projected_centralizer_mem {G U Q : Type*} [Group G] [Group U] [Group Q]
    (H : Subgroup G) (f : H→*Q) (i : U→*H) (R : Subgroup G) (S : Subgroup H)
    (hS : ∀x : H,x∈S→x.val∈R) (u : U)
    (hu : (H.subtype.comp i) u∈Subgroup.centralizer (R : Set G)) :
    (f.comp i) u∈Subgroup.centralizer (S.map f : Set Q) := by
  apply Subgroup.mem_centralizer_iff.mpr
  rintro _ ⟨x,hx,rfl⟩
  have he : x*i u=i u*x := Subtype.ext
    ((Subgroup.mem_centralizer_iff.mp hu) x.val (hS x hx))
  simpa only [map_mul] using congrArg f he

def matrixRootCentralizer (q : CFSG.PrimePower) (k : Roots CartanMatrix.E₆) :
    Subgroup (signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) false) :=
  (Subgroup.centralizer (RootLine (q.Extension 2) k : Set _)).comap
    (signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) false).subtype

def originalRootCentralizer (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (k : Roots CartanMatrix.E₆) :
    Subgroup (signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) false) :=
  (Subgroup.centralizer (originalRootLine q k : Set _)).comap (fixedPositiveToOriginal q)

theorem matrixRootCentralizer_le_original (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (k : Roots CartanMatrix.E₆) :
    matrixRootCentralizer q k≤originalRootCentralizer q k := by
  intro u hu
  have hS : ∀x : fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2),
      x∈rootLineInGenerated q k→x.val∈RootLine (q.Extension 2) k := by
    intro x hx
    change x.val∈fixedRootLine (q.Extension 2) (definingFieldAutomorphism q 2) k at hx
    exact hx.1
  have hm := projected_centralizer_mem
    (fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2))
    (generatedToOriginal q) (fixedPositiveToGenerated q) (RootLine (q.Extension 2) k)
    (rootLineInGenerated q k) hS u hu
  change fixedPositiveToOriginal q u∈Subgroup.centralizer (originalRootLine q k : Set _)
  rw [fixedPositiveToOriginal_apply]
  exact hm

theorem matrixRootCentralizer_card_le_original (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (k : Roots CartanMatrix.E₆) :
    Nat.card (matrixRootCentralizer q k)≤Nat.card (originalRootCentralizer q k) :=
  Nat.card_le_card_of_injective
    (Subgroup.inclusion (matrixRootCentralizer_le_original q k))
    (Subgroup.inclusion_injective (matrixRootCentralizer_le_original q k))

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRootCentralizer
