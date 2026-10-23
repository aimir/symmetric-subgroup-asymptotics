import SymmetricSubgroupAsymptotics.CFSGFFourE6SignedOriginalProjection
import SymmetricSubgroupAsymptotics.CFSGE6GeckSignedSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveRootUnits
import SymmetricSubgroupAsymptotics.CFSGFFourE6NegativeRootUnits
import Mathlib.Algebra.Group.Subgroup.Finite

/-! All eight actual signed simple-root parameter charts in the ORIGINAL
F4 model. Every chart has |K| elements. In particular no root-length
preservation is inferred from a cardinal distinction, and characteristic
two length-interchanging graph/field automorphisms are not excluded. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalSimpleParameters
open CFSGFFourSerreMatrices CFSGFFourE6SignedOriginalProjection
open CFSGFFourE6OriginalOppositeAlignment CFSGFFourE6OriginalProjection
open CFSGFFourE6RootSubgroups CFSGFFourE6DiagramFixed CFSGFFourE6PositiveRootUnits
open CFSGFFourE6NegativeRootUnits CFSGE6GeckSignedSimpleParameters
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckPositiveTwist
open CFSGSerreQuadraticMatrix CFSG.Models.Chevalley

def foldedFixedHom (K : Type) [Field K] (neg : Bool) (i : Fin 4) :
    Multiplicative K→*signedFixed K (RingEquiv.refl K) neg where
  toFun a := ⟨canonicalRoot realizationData K neg i a.toAdd,
    ⟨foldedRootGroup_le_ambient K neg (folded_root_mem K neg i a.toAdd),
      folded_root_fixed K neg i a.toAdd⟩⟩
  map_one' := Subtype.ext (canonicalRoot_zero realizationData K neg i)
  map_mul' a b := Subtype.ext (canonicalRoot_add realizationData K neg i a.toAdd b.toAdd).symm

theorem foldedFixedHom_val_as_raw (K : Type) [Field K] (neg : Bool) (i : Fin 4)
    (a : Multiplicative K) : (foldedFixedHom K neg i a).val=
      ![rawPairedHom K (RingEquiv.refl K) neg 0 a,
        rawPairedHom K (RingEquiv.refl K) neg 1 a,
        rawSingletonHom K neg 1 a,rawSingletonHom K neg 0 a] i := by
  change canonicalRoot realizationData K neg i a.toAdd=_
  cases neg
  · rw [folded_positive_root]
    fin_cases i <;> rfl
  · rw [folded_negative_root]
    fin_cases i <;> rfl

theorem foldedFixedHom_injective (K : Type) [Field K] (neg : Bool) (i : Fin 4) :
    Function.Injective (foldedFixedHom K neg i) := by
  intro a b he
  have hh := congrArg (fun z : signedFixed K (RingEquiv.refl K) neg=>z.val) he
  dsimp only at hh
  rw [foldedFixedHom_val_as_raw,foldedFixedHom_val_as_raw] at hh
  fin_cases i
  · exact rawPaired_injective K (RingEquiv.refl K) neg 0 hh
  · exact rawPaired_injective K (RingEquiv.refl K) neg 1 hh
  · exact rawSingleton_injective K neg 1 hh
  · exact rawSingleton_injective K neg 0 hh

def originalSimpleHom (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (neg : Bool) (i : Fin 4) :
    Multiplicative K→*Projective CartanMatrix.F₄ K :=
  (signedFixedToOriginal K neg).comp (foldedFixedHom K neg i)

theorem originalSimpleHom_apply (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (neg : Bool) (i : Fin 4)
    (a : Multiplicative K) : originalSimpleHom K neg i a=
      foldedToOriginal K (canonicalElementaryRoot realizationData K neg i a.toAdd) := rfl

theorem originalSimpleHom_injective (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (neg : Bool) (i : Fin 4) : Function.Injective (originalSimpleHom K neg i) :=
  (signedFixedToOriginal_injective K p neg).comp (foldedFixedHom_injective K neg i)

theorem originalSimpleHom_range_card (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (neg : Bool) (i : Fin 4) : Nat.card (originalSimpleHom K neg i).range=Nat.card K := by
  calc
    _=Nat.card (Multiplicative K) :=
      (Nat.card_congr (MonoidHom.ofInjective (originalSimpleHom_injective K p neg i)).toEquiv).symm
    _=_ := Nat.card_congr Multiplicative.toAdd

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalSimpleParameters
