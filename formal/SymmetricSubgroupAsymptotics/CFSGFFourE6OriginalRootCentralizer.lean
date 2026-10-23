import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalRootFamily
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! Full raw matrix root-line centralizers in the literal fixed E6 upper
group project into the corresponding ORIGINAL F4 centralizers. This
actual inclusion transfers capacity without full-source faithfulness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalRootCentralizer
open CFSGFFourE6OriginalRootFamily CFSGFFourE6FixedPositiveProjection
open CFSGFFourE6OriginalProjection CFSGFFourSerreMatrices
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckFixedRootFamilyCover
open CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix CFSG.Models.Chevalley

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

def matrixRootCentralizer (K : Type) [Field K] (k : Roots CartanMatrix.E₆) :
    Subgroup (signedFixed K (RingEquiv.refl K) false) :=
  (Subgroup.centralizer (RootLine K k : Set _)).comap
    (signedFixed K (RingEquiv.refl K) false).subtype

def originalRootCentralizer (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (k : Roots CartanMatrix.E₆) : Subgroup (signedFixed K (RingEquiv.refl K) false) :=
  (Subgroup.centralizer (originalRootLine K k : Set _)).comap (fixedPositiveToOriginal K p)

theorem matrixRootCentralizer_le_original (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (k : Roots CartanMatrix.E₆) : matrixRootCentralizer K k≤originalRootCentralizer K p k := by
  intro u hu
  have hS : ∀x : canonicalElementaryGroup realizationData K,
      x∈rootLineInFolded K k→x.val∈RootLine K k := by
    intro x hx
    change x.val∈fixedRootLine K (RingEquiv.refl K) k at hx
    exact hx.1
  have hm := projected_centralizer_mem (canonicalElementaryGroup realizationData K)
    (foldedToOriginal K) (fixedPositiveToFolded K) (RootLine K k)
    (rootLineInFolded K k) hS u hu
  change fixedPositiveToOriginal K p u∈Subgroup.centralizer (originalRootLine K k : Set _)
  rw [fixedPositiveToOriginal_apply]
  exact hm

theorem matrixRootCentralizer_card_le_original (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (k : Roots CartanMatrix.E₆) :
    Nat.card (matrixRootCentralizer K k)≤Nat.card (originalRootCentralizer K p k) :=
  Nat.card_le_card_of_injective (Subgroup.inclusion (matrixRootCentralizer_le_original K p k))
    (Subgroup.inclusion_injective (matrixRootCentralizer_le_original K p k))

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalRootCentralizer
