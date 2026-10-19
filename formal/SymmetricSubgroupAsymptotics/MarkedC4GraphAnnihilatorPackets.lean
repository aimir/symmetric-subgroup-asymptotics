import SymmetricSubgroupAsymptotics.MarkedC4OriginalGraphAnnihilators
import SymmetricSubgroupAsymptotics.MarkedC4SubgroupCharacterGraph

/-! A constructed, injective graph-first quotient packet for a fixed
physical word. The finite normal menu depends ONLY on the physical letters.
One global mark group is retained in the quotient packet. Every original
subgroup and complete character is recovered; no descent is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.GraphAnnihilatorPackets
open FiniteOrbitWordShapes FiniteBinaryWordTargets

variable {C b : ℕ} (T : Target C b) (M : Type) [Group M]
abbrev Ambient := Product T.letters

/-- Literal original subdirect subgroups and their whole global character. -/
abbrev Object := {z : (Σ H : Subgroup (Ambient T),H →* M) //
  ∀ i,Function.Surjective (fun h : z.1 => h.val i)}

/-- This menu is independent of M, its rank, or any selected character. -/
abbrev Menu := ∀ i : Fin T.shape.length.val,
  {N : Subgroup (T.letters i) // N.Normal}
instance : Finite (Menu T) := inferInstance
instance : Fintype (Menu T) := Fintype.ofFinite _

def physicalProduct (N : Menu T) : Subgroup (Ambient T) :=
  Subgroup.pi Set.univ (fun i => (N i).val)

instance menuProductNormal (N : Menu T) : (physicalProduct T N).Normal := by
  refine ⟨?_⟩
  intro n hn g i _
  exact (N i).property.conj_mem (n i) (hn i (Set.mem_univ i)) (g i)

def quotientMap (N : Menu T) :
    (Ambient T × M) →* ((Ambient T ⧸ physicalProduct T N) × M) :=
  (QuotientGroup.mk' (physicalProduct T N)).prodMap (MonoidHom.id M)

abbrev Packet := Σ N : Menu T,Subgroup ((Ambient T ⧸ physicalProduct T N) × M)

/-- Reading a packet recovers a literal subgroup of the ORIGINAL product
with its SAME global mark coordinates. -/
def decode (p : Packet T M) : Subgroup (Ambient T × M) :=
  p.2.comap (quotientMap T M p.1)

def actualTarget (z : Object T M) : Target C b where
  shape := T.shape
  letters := T.letters
  binary := T.binary
  transitive := T.transitive
  image := z.val.1
  subdirect := z.property

def actualMenu (z : Object T M) : Menu T := fun i =>
  ⟨OriginalGraphAnnihilators.factor (actualTarget T M z) z.val.2 i,
    OriginalGraphAnnihilators.factor_normal (actualTarget T M z) z.val.2 i⟩

/-- Actual annihilator selection followed by the actual quotient graph.
The selection MAY depend on the character; the physical menu does not. -/
def code (z : Object T M) : Packet T M :=
  ⟨actualMenu T M z,
    (SubgroupCharacterGraph.graph z.val.1 z.val.2).map
      (quotientMap T M (actualMenu T M z))⟩

/-- Kernel containment proved for the actual annihilators gives exact
original graph recovery from the selected normal menu and quotient graph. -/
theorem recover (z : Object T M) :
    decode T M (code T M z)=SubgroupCharacterGraph.graph z.val.1 z.val.2 := by
  exact OriginalGraphAnnihilators.recover_graph (actualTarget T M z) z.val.2

/-- This is the required ORIGINAL marked-pair injection, not an assumed
encoding or an inequality on independently maximized restrictions. -/
theorem code_injective : Function.Injective (code T M) := by
  intro z w he
  apply Subtype.ext
  apply SubgroupCharacterGraph.code_injective
  have hh := congrArg (decode T M) he
  exact (recover T M z).symm.trans (hh.trans (recover T M w))

/-- Exact finite incidence bound; menu multiplicities and all characters
are retained in the actual packet target. -/
theorem card_le [Finite M] : Nat.card (Object T M) ≤ Nat.card (Packet T M) :=
  Nat.card_le_card_of_injective (code T M) (code_injective T M)

end SymmetricSubgroupAsymptotics.MarkedC4.GraphAnnihilatorPackets
