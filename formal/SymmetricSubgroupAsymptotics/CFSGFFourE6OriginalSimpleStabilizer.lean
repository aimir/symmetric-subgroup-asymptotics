import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalPairAlignment
import SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyStabilizer

/-! Literal original opposed-Sylow and signed-simple-chart stabilizers.
The definitions build in no permutation or field action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalSimpleStabilizer
open CFSGFFourE6OriginalSimpleParameters CFSGFFourE6OriginalProjection
open CFSGFFourE6OriginalOppositeAlignment CFSGSubgroupFamilyStabilizer CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)]

def pairStabilizer : Subgroup (MulAut (Projective CartanMatrix.F₄ K)) :=
  familyStabilizer (fun neg : Bool => if neg then originalNegative K
    else (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)))

def simpleStabilizer : Subgroup (pairStabilizer K p) :=
  (familyStabilizer (fun z : Bool×Fin 4 => (originalSimpleHom K z.1 z.2).range)).subgroupOf
    (pairStabilizer K p)

def simpleStabilizerAction : simpleStabilizer K p→*MulAut (Projective CartanMatrix.F₄ K) :=
  (pairStabilizer K p).subtype.comp (simpleStabilizer K p).subtype

theorem pair_preserves_positive (f : pairStabilizer K p) :
    (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)).map f.val.toMonoidHom=
      (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)) := f.property false

theorem pair_preserves_negative (f : pairStabilizer K p) :
    (originalNegative K).map f.val.toMonoidHom=originalNegative K := f.property true

theorem simple_preserves_chart (f : simpleStabilizer K p) (neg : Bool) (i : Fin 4) :
    (originalSimpleHom K neg i).range.map (simpleStabilizerAction K p f).toMonoidHom=
      (originalSimpleHom K neg i).range := f.property (neg,i)

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalSimpleStabilizer
