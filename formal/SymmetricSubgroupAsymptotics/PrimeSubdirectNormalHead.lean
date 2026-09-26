import SymmetricSubgroupAsymptotics.PrimeSubdirectRank
import SymmetricSubgroupAsymptotics.RelativeAmbientTransport
import Mathlib.GroupTheory.Commutator.Basic

/-! Relative heads of actual normal subgroups in a full subdirect product.
The two terms use the original normal image in the second factor and the
literal first-axis kernel, with conjugation by the entire corresponding
factor. No splitting, numerical rank bound or carrier acceptance is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace SubdirectNormalHead

variable {A B : Type*} [Group A] [Group B]
    (K : Subgroup (A × B)) (M : Subgroup K)

def firstProjection : K →* A := (MonoidHom.fst A B).comp K.subtype

/-- The exact original image of the normal subgroup in the second factor. -/
def secondImage : Subgroup B := M.map (subdirectSecond K)

/-- The first image of precisely the elements of M with second coordinate
one. The equality with the literal Goursat axis is proved below. -/
def firstAxis : Subgroup A :=
  (M ⊓ (subdirectSecond K).ker).map (firstProjection K)

@[simp] theorem mem_firstAxis (a : A) : a ∈ firstAxis K M ↔
    ∃ ha : (a, (1 : B)) ∈ K, (⟨(a,1),ha⟩ : K) ∈ M := by
  constructor
  · rintro ⟨⟨⟨x,y⟩,hxy⟩,⟨hm,hsecond⟩,hfirst⟩
    change y=1 at hsecond
    change x=a at hfirst
    subst x
    subst y
    exact ⟨hxy,hm⟩
  · rintro ⟨ha,hm⟩
    exact ⟨⟨(a,1),ha⟩,⟨hm,rfl⟩,rfl⟩

theorem firstAxis_eq_goursatFst : firstAxis K M=(M.map K.subtype).goursatFst := by
  ext a
  rw [mem_firstAxis,Subgroup.mem_goursatFst]
  constructor
  · rintro ⟨ha,hm⟩
    exact ⟨⟨(a,1),ha⟩,hm,rfl⟩
  · rintro ⟨m,hm,he⟩
    have ha : (a, (1 : B)) ∈ K := he ▸ m.2
    refine ⟨ha,?_⟩
    exact (Subtype.ext he : m=⟨(a,1),ha⟩) ▸ hm

theorem firstAxis_le : firstAxis K M≤K.goursatFst := by
  intro a ha
  obtain ⟨ha,_⟩ := (mem_firstAxis K M a).mp ha
  exact Subgroup.mem_goursatFst.mpr ha

theorem firstAxis_normal [M.Normal]
    (hA : Function.Surjective (Prod.fst ∘ K.subtype)) : (firstAxis K M).Normal :=
  Subgroup.Normal.map inferInstance (firstProjection K) hA

theorem secondImage_normal [M.Normal]
    (hB : Function.Surjective (Prod.snd ∘ K.subtype)) : (secondImage K M).Normal :=
  Subgroup.Normal.map inferInstance (subdirectSecond K) hB

/-- The actual restricted projection onto its exact original image. -/
def projection : M →* secondImage K M where
  toFun m := ⟨subdirectSecond K (m : K),⟨m,m.2,rfl⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem projection_surjective : Function.Surjective (projection K M) := by
  rintro ⟨b,m,hm,rfl⟩
  exact ⟨⟨m,hm⟩,rfl⟩

/-- The kernel equivalence fixes the first physical coordinate. -/
def kernelEquiv : (projection K M).ker ≃* firstAxis K M where
  toFun n := ⟨((n.1 : M) : K).1.1,
    ⟨((n.1 : M) : K),⟨(n.1 : M).2,congrArg Subtype.val n.2⟩,rfl⟩⟩
  invFun a :=
    let ha := (mem_firstAxis K M (a : A)).mp a.2
    ⟨⟨⟨((a : A),1),Classical.choose ha⟩,Classical.choose_spec ha⟩,rfl⟩
  left_inv n := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (congrArg Subtype.val n.2).symm
  right_inv _ := rfl
  map_mul' _ _ := rfl

section Characters
variable (p : ℕ) [Fact p.Prime] [M.Normal]
    [(secondImage K M).Normal] [(firstAxis K M).Normal]

/-- The target action is induced by the actual second projection. -/
def targetAction : K →* MulAut (secondImage K M) :=
  MulAut.conjNormal.comp (subdirectSecond K)

theorem projection_equivariant (k : K) (m : M) :
    projection K M (normalChainSourceAction M k m)=
      targetAction K M k (projection K M m) := by
  apply Subtype.ext
  change subdirectSecond K (k*(m : K)*k⁻¹)=
    subdirectSecond K k * subdirectSecond K (m : K) * (subdirectSecond K k)⁻¹
  simp only [map_mul,map_inv]

/-- Kernel characters retain conjugation by all of A. A conjugating
lift comes from the whole original subdirect core K, not from M. -/
def kernelCharacterMap (hA : Function.Surjective (Prod.fst ∘ K.subtype)) :
    primeActionKernelCharacters p (projection K M) (normalChainSourceAction M)
      (targetAction K M) (projection_equivariant K M) →ₗ[ZMod p]
        primeRelativeCharacters p (firstAxis K M) := by
  refine {
    toFun := fun χ => ⟨χ.1.comp (kernelEquiv K M).symm.toMonoidHom.toAdditive,?_⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  intro a n
  obtain ⟨k,hk⟩ := hA a
  have h := χ.2 k ((kernelEquiv K M).symm n)
  have he : (kernelEquiv K M).symm
      (⟨a*(n : A)*a⁻¹,Subgroup.Normal.conj_mem inferInstance _ n.2 a⟩ : firstAxis K M)=
      (⟨normalChainSourceAction M k ((kernelEquiv K M).symm n : M),by
        change projection K M
          (normalChainSourceAction M k ((kernelEquiv K M).symm n : M))=1
        rw [projection_equivariant,((kernelEquiv K M).symm n).2,map_one]⟩ :
          (projection K M).ker) := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · change a*(n : A)*a⁻¹=(k : A × B).1*(n : A)*((k : A × B).1)⁻¹
      rw [show (k : A × B).1=a from hk]
    · change (1 : B)=(k : A × B).2*1*((k : A × B).2)⁻¹
      simp
  exact (congrArg (fun z : (projection K M).ker => χ.1 (Additive.ofMul z)) he).trans h

theorem kernelCharacterMap_injective
    (hA : Function.Surjective (Prod.fst ∘ K.subtype)) :
    Function.Injective (kernelCharacterMap K M p hA) := by
  intro χ ψ h
  apply Subtype.ext
  apply primeCharacterInflation_injective p (kernelEquiv K M).symm.toMonoidHom
    (kernelEquiv K M).symm.surjective
  simpa only [kernelCharacterMap,primeCharacterInflation] using congrArg Subtype.val h

end Characters

/-- Any original normal subgroup in a full subdirect product satisfies
the relative-head extension bound on its exact two original factors. -/
theorem relativeHead_le (p : ℕ) [Fact p.Prime] [Finite A] [Finite B] [M.Normal]
    (hA : Function.Surjective (Prod.fst ∘ K.subtype))
    (hB : Function.Surjective (Prod.snd ∘ K.subtype)) :
    letI := firstAxis_normal K M hA
    letI := secondImage_normal K M hB
    Module.finrank (ZMod p) (primeRelativeCharacters p M)≤
      Module.finrank (ZMod p) (primeRelativeCharacters p (secondImage K M))+
        Module.finrank (ZMod p) (primeRelativeCharacters p (firstAxis K M)) := by
  letI := firstAxis_normal K M hA
  letI := secondImage_normal K M hB
  have h := primeActionCharacterRank_extension_le p (projection K M)
    (normalChainSourceAction M) (targetAction K M) (projection_equivariant K M)
    (projection_surjective K M)
  have hs := (normalChainSourceCharactersEquiv M p).finrank_eq
  have ht := (relativeActionCharactersEquiv p (subdirectSecond K) hB
    (secondImage K M)).finrank_eq
  change Module.finrank (ZMod p) (primeActionCharacters p (targetAction K M))=
    Module.finrank (ZMod p) (primeRelativeCharacters p (secondImage K M)) at ht
  rw [hs,ht] at h
  have hk := (kernelCharacterMap K M p hA).finrank_le_finrank_of_injective
    (kernelCharacterMap_injective K M p hA)
  exact h.trans (Nat.add_le_add_left hk _)

private theorem map_derived_le {G H : Type*} [Group G] [Group H] (f : G →* H) :
    (commutator G).map f≤commutator H := by
  rw [map_commutator_eq,commutator_def]
  exact Subgroup.commutator_mono le_top le_top

/-- Derived normals have derived images in each original factor. -/
theorem secondImage_le_commutator (hM : M≤commutator K) :
    secondImage K M≤commutator B :=
  (Subgroup.map_mono hM).trans (map_derived_le (subdirectSecond K))

theorem firstAxis_le_commutator (hM : M≤commutator K) :
    firstAxis K M≤commutator A :=
  (Subgroup.map_mono (inf_le_left.trans hM)).trans (map_derived_le (firstProjection K))

end SubdirectNormalHead
end SymmetricSubgroupAsymptotics
