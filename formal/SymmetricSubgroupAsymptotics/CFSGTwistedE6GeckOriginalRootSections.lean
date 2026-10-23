import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSourceWordAction
import SymmetricSubgroupAsymptotics.CFSGTwistedE6NegativeSimpleSectionWitness

/-! Every positive E6 root receives an actual ORIGINAL fixed conjugator.
Singleton and paired root sections are built in the original pinned fixed
group and their matrix-image actions are calculated literally. These are
source witnesses, not lifts inferred from matrix fixedness. Derived
membership and whole fixed-upper generation remain separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRootSections
open CFSGTwistedE6GeckSourceWordAction CFSGTwistedE6FixedWeylWords
open CFSGTwistedE6NegativeSimpleSectionWitness CFSGTwistedE6FixedWordClassification
open CFSGTwistedE6GeckSourceAction CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6FixedA2 CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoGeckWeylWordAlgebra CFSGNormTwoGeckWeylLatticeLinear
open CFSGSerreQuadraticMatrix CFSGSerreFixedRootElements CFSGSerreOrdinaryTwists

abbrev PositiveRoot := {k : Roots CartanMatrix.E₆ // ∀i,0 ≤ k.val i}

def sectionWitness (k : PositiveRoot) :
    {z : List (Fin 4)×Fin 6 //
      wordLinear CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index
        (inverseWord (expandRelative z.1)) (-(E6Index z.2:Roots CartanMatrix.E₆).val)=k.val.val} :=
  Classical.choice (by
    obtain ⟨r,j,h⟩ := exists_relative_inverse_negative_degree k.val k.property
    exact ⟨⟨(r,j),h⟩⟩)

abbrev sectionRelative (k : PositiveRoot) := (sectionWitness k).val.1
abbrev sectionNode (k : PositiveRoot) := (sectionWitness k).val.2

theorem section_degree (k : PositiveRoot) :
    wordLinear CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index
      (inverseWord (expandRelative (sectionRelative k)))
      (-(E6Index (sectionNode k):Roots CartanMatrix.E₆).val)=k.val.val :=
  (sectionWitness k).property

def sourceTransport (q : CFSG.PrimePower) (k : PositiveRoot) : Fixed q :=
  (sourceRelativeWord q (sectionRelative k))⁻¹

def matrixTransport (q : CFSG.PrimePower) (k : PositiveRoot) : MatrixGroup (q.Extension 2) :=
  (matrixWord (q.Extension 2) (expandRelative (sectionRelative k)))⁻¹

theorem sourceTransport_action (q : CFSG.PrimePower) (k : PositiveRoot) :
    imageAction q (sourceTransport q k)=matrixAction (q.Extension 2) (matrixTransport q k) := by
  simp only [sourceTransport,matrixTransport,map_inv,sourceRelativeWord_action]

theorem nonfixed_node_cartan_zero : ∀j : Fin 6,CFSG.Models.e6Twist j≠j→
    CartanMatrix.E₆ j (CFSG.Models.e6Twist j)=0 := by decide

theorem node_orbit_two : ∀j : Fin 6,CFSG.Models.e6Twist (CFSG.Models.e6Twist j)=j := by decide

def singletonAt (q : CFSG.PrimePower) (j : Fin 6) (hj : CFSG.Models.e6Twist j=j)
    (t : q.Extension 2) (ht : t^q.order=t) : Fixed q :=
  fixedRoot CartanMatrix.E₆ (q.Extension 2) CFSG.Models.e6Twist (fun _=>q.order) true j t hj ht

def pairAt (q : CFSG.PrimePower) (j : Fin 6) (hj : CFSG.Models.e6Twist j≠j)
    (t : q.Extension 2) : Fixed q :=
  CFSGSerrePairedFixedRoots.pairedFixedRoot CartanMatrix.E₆ (q.Extension 2)
    CFSG.Models.e6Twist (fun _=>q.order) true j (nonfixed_node_cartan_zero j hj)
    (node_orbit_two j) t (CFSGTwistedANaturalMatrices.extension_two_pow_twice q t)

theorem singletonAt_action (q : CFSG.PrimePower) (j : Fin 6) (hj : CFSG.Models.e6Twist j=j)
    (t : q.Extension 2) (ht : t^q.order=t) :
    imageAction q (singletonAt q j hj t ht)=
      matrixAction (q.Extension 2) (canonicalElementaryRoot rawData (q.Extension 2) true j t) :=
  source_root_action (q.Extension 2) true j t

theorem pairAt_action (q : CFSG.PrimePower) (j : Fin 6) (hj : CFSG.Models.e6Twist j≠j)
    (t : q.Extension 2) :
    imageAction q (pairAt q j hj t)=matrixAction (q.Extension 2)
      (canonicalElementaryRoot rawData (q.Extension 2) true j t*
        canonicalElementaryRoot rawData (q.Extension 2) true (CFSG.Models.e6Twist j) (t^q.order)) := by
  change imageRepresentation data (q.Extension 2)
    (modelRoot CartanMatrix.E₆ (q.Extension 2) true j t*
      modelRoot CartanMatrix.E₆ (q.Extension 2) true (CFSG.Models.e6Twist j) (t^q.order))=_
  rw [map_mul,source_root_action,source_root_action,map_mul]

def singletonSection (q : CFSG.PrimePower) (k : PositiveRoot)
    (hj : CFSG.Models.e6Twist (sectionNode k)=sectionNode k)
    (t : q.Extension 2) (ht : t^q.order=t) : Fixed q :=
  sourceTransport q k*singletonAt q (sectionNode k) hj t ht*(sourceTransport q k)⁻¹

def pairedSection (q : CFSG.PrimePower) (k : PositiveRoot)
    (hj : CFSG.Models.e6Twist (sectionNode k)≠sectionNode k) (t : q.Extension 2) : Fixed q :=
  sourceTransport q k*pairAt q (sectionNode k) hj t*(sourceTransport q k)⁻¹

theorem singletonSection_action (q : CFSG.PrimePower) (k : PositiveRoot)
    (hj : CFSG.Models.e6Twist (sectionNode k)=sectionNode k)
    (t : q.Extension 2) (ht : t^q.order=t) :
    imageAction q (singletonSection q k hj t ht)=matrixAction (q.Extension 2)
      (matrixTransport q k*canonicalElementaryRoot rawData (q.Extension 2) true (sectionNode k) t*
        (matrixTransport q k)⁻¹) := by
  simp only [singletonSection,map_mul,map_inv,sourceTransport_action,singletonAt_action]

theorem pairedSection_action (q : CFSG.PrimePower) (k : PositiveRoot)
    (hj : CFSG.Models.e6Twist (sectionNode k)≠sectionNode k) (t : q.Extension 2) :
    imageAction q (pairedSection q k hj t)=matrixAction (q.Extension 2)
      (matrixTransport q k*(canonicalElementaryRoot rawData (q.Extension 2) true (sectionNode k) t*
        canonicalElementaryRoot rawData (q.Extension 2) true (CFSG.Models.e6Twist (sectionNode k))
          (t^q.order))*(matrixTransport q k)⁻¹) := by
  simp only [pairedSection,map_mul,map_inv,sourceTransport_action,pairAt_action]

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRootSections
