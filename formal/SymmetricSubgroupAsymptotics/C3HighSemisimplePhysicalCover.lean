import SymmetricSubgroupAsymptotics.TernaryHighSemisimpleOwnerWithoutCatalogue
import SymmetricSubgroupAsymptotics.C3PhysicalStructuralOwner
import SymmetricSubgroupAsymptotics.C3HighNestedCarrier
import SymmetricSubgroupAsymptotics.LocalSemisimpleRoundingTransport

/-! A separate high-C3 sector keeps the actual degree10/12 nonaffine orbit.
The outer regular C3 stays in the untouched complement. The cover uses the
finite set of literal actions, each carrying a proved actual-kernel rounding
datum; no finite classification or canonical action recognition is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

/-- The actual high semisimple orbit on a complete original physical group. -/
def C3PhysicalHighSemisimpleOwner (n : ℕ)
    (G : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  ∃ (b : ℕ) (e : TernaryCyclic⊕Fin b≃Fin n)
    (H : Subgroup (ternaryRegularAction×Equiv.Perm (Fin b))),
    relabelSubgroup e (H.map (fusionOrbitAction ternaryRegularAction))=G ∧
    H.map (MonoidHom.fst ternaryRegularAction (Equiv.Perm (Fin b)))=⊤ ∧
    ∃ o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H),
    ∃ (N : Subgroup (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o))
      (hN : N.Normal),
      letI := hN
      3*Nat.card o.orbit<20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ∧
      TernaryHighPrimitiveSemisimpleOwner
        (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o) o.orbit

theorem c3TrivialHigh_enters_structural_or_semisimple_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (b n : ℕ) (e : TernaryCyclic⊕Fin b≃Fin n)
    (P : Subgroup (ternaryRegularAction×Equiv.Perm (Fin b)) → Prop)
    (H : Subgroup (ternaryRegularAction×Equiv.Perm (Fin b)))
    (hH : C3TrivialHighPredicate b P H) :
    C3PhysicalStructuralOwner n (relabelSubgroup e (C3HighNestedCarrier.physicalSubgroup H)) ∨
      C3PhysicalHighSemisimpleOwner n
        (relabelSubgroup e (C3HighNestedCarrier.physicalSubgroup H)) := by
  obtain ⟨o,N,hN,hHigh⟩ := c3TrivialHigh_actualOrbit_witness b P H hH
  let A := OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o
  letI : MulAction.IsPretransitive A o.orbit := orbitImage_pretransitive (C3ComplementSource b H) o
  letI : N.Normal := hN
  rcases ternaryHigh_earlierOwner_or_semisimple_without_catalogue
    hChief hWeight hgen hindex published8 h18 N hHigh with hOld|hNew
  · exact Or.inl ⟨b,e,H,rfl,hH.1.1,o,N,hN,hHigh,hOld⟩
  · exact Or.inr ⟨b,e,H,rfl,hH.1.1,o,N,hN,hHigh,hNew⟩

def c3SemisimpleHighWidth (d : Fin 2) : ℕ := if d=0 then 10 else 12

/-- Fixed finite literal actions with their actual semisimple compression.
No census or model locator is a premise of this finite index. -/
abbrev C3HighSemisimpleIndex :=
  Σ d : Fin 2,{U : Subgroup (Equiv.Perm (Fin (c3SemisimpleHighWidth d))) //
    Nonempty (LocalSemisimpleRoundingCompressionData U (c3SemisimpleHighWidth d))}

instance c3HighSemisimpleIndexFinite : Finite C3HighSemisimpleIndex := by
  infer_instance

def c3HighSemisimpleAction (j : C3HighSemisimpleIndex) := j.2.1

def c3HighSemisimpleCompression (j : C3HighSemisimpleIndex) :
    LocalSemisimpleRoundingCompressionData (c3HighSemisimpleAction j)
      (c3SemisimpleHighWidth j.1) := Classical.choice j.2.2

/-- Delete precisely the retained actual orbit. The full original subgroup,
outer regular C3, all untouched points and their correlations are retained. -/
theorem c3PhysicalHighSemisimpleOwner_finiteFusionCover
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (hG : C3PhysicalHighSemisimpleOwner n G) :
    ∃ j : C3HighSemisimpleIndex,∃ hn : c3SemisimpleHighWidth j.1≤n,
      G∈FusionWidthCanonicalFamily (c3HighSemisimpleAction j) hn (fun _ => True) := by
  rcases hG with ⟨b,e,H,hphysical,hfull,o,N,hN,hHigh,hOwner⟩
  have hdegree : b+3=n := by
    have hcard := Nat.card_congr e
    have hc : Nat.card TernaryCyclic=3 := by
      rw [Nat.card_congr RepeatedMarkerOwnerBound.ternaryFinEquiv,Nat.card_fin]
    rw [Nat.card_sum,hc,Nat.card_fin,Nat.card_fin] at hcard
    omega
  subst n
  let A := OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o
  let C : C3HighNestedCarrier.Data H := ⟨o,N,hN,hHigh⟩
  obtain ⟨d,hd⟩ : ∃ d : Fin 2,c3SemisimpleHighWidth d=Nat.card o.orbit := by
    rcases hOwner.2.1 with h10|h12
    · exact ⟨0,by simpa only [c3SemisimpleHighWidth,if_pos rfl] using h10.symm⟩
    · exact ⟨1,by simpa only [c3SemisimpleHighWidth,if_neg (by decide : (1 : Fin 2)≠0)] using h12.symm⟩
  let lab : o.orbit≃Fin (c3SemisimpleHighWidth d) := Finite.equivFinOfCardEq hd.symm
  let U := relabelSubgroup lab A
  let a : A≃*U := lab.permCongrHom.subgroupMap A
  let comp : LocalSemisimpleRoundingCompressionData U (c3SemisimpleHighWidth d) := by
    have cc := (hOwner.compression hindex published8).comapEquiv a.symm
    exact cc.changeWidth hd.symm
  let j : C3HighSemisimpleIndex := ⟨d,U,⟨comp⟩⟩
  have hwidth : Nat.card C.orbit.orbit=c3SemisimpleHighWidth d := hd.symm
  have hn : c3SemisimpleHighWidth d≤b+3 := by
    have hh := C3HighNestedCarrier.width_le H o hd.symm
    omega
  refine ⟨j,hn,?_⟩
  rw [←hphysical]
  exact C3HighNestedCarrier.mem_widthCanonicalFamily_of_relabel H C hwidth U lab.symm
    (relabelSubgroup_symm lab A) e (fun _ => True) trivial

end SymmetricSubgroupAsymptotics
