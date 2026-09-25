import SymmetricSubgroupAsymptotics.PrimeRelativeCharacters
import Mathlib.GroupTheory.Goursat

/-! Actual subdirect pair cores admit the correct relative-head rank step.
The kernel of the second projection is identified with the literal normal
axis of the first action. Its ambient conjugation is retained. The factors
may be nonabelian, and no direct-product replacement of the core is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {A B : Type*} [Group A] [Group B]

def subdirectSecond (K : Subgroup (A×B)) : K →* B :=
  (MonoidHom.snd A B).comp K.subtype

/-- The actual second-projection kernel is the original first-axis subgroup. -/
def subdirectKernelEquiv (K : Subgroup (A×B)) :
    (subdirectSecond K).ker ≃* K.goursatFst where
  toFun x := ⟨(x.1:A×B).1,Subgroup.mem_goursatFst.mpr (by
    have hx : (x.1:A×B).2=1 := x.2
    simpa only [← hx] using x.1.2)⟩
  invFun a := ⟨⟨((a:A),1),Subgroup.mem_goursatFst.mp a.2⟩,rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact x.2.symm
  right_inv a := rfl
  map_mul' a b := rfl

variable (p : ℕ) [Fact p.Prime]

/-- Every relative kernel character descends to the original axis action.
Full first projection is used to lift each ambient conjugating element. -/
def subdirectRelativeCharacterMap (K : Subgroup (A×B))
    (hA : Function.Surjective (Prod.fst ∘ K.subtype)) :
    letI := Subgroup.normal_goursatFst hA
    primeRelativeCharacters p (subdirectSecond K).ker →ₗ[ZMod p]
      primeRelativeCharacters p K.goursatFst := by
  letI := Subgroup.normal_goursatFst hA
  refine {
    toFun := fun χ => ⟨χ.1.comp (subdirectKernelEquiv K).symm.toMonoidHom.toAdditive,?_⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  intro a n
  obtain ⟨k,hk⟩ := hA a
  have h := χ.2 k ((subdirectKernelEquiv K).symm n)
  have he : (subdirectKernelEquiv K).symm
      (⟨a*(n:A)*a⁻¹,Subgroup.Normal.conj_mem inferInstance _ n.2 a⟩:K.goursatFst) =
      (⟨k*((subdirectKernelEquiv K).symm n:K)*k⁻¹,
        Subgroup.Normal.conj_mem inferInstance _ ((subdirectKernelEquiv K).symm n).2 k⟩:
          (subdirectSecond K).ker) := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · change a*(n:A)*a⁻¹ = (k:A×B).1*(n:A)*((k:A×B).1)⁻¹
      rw [show (k:A×B).1=a from hk]
    · change 1=(k:A×B).2*1*((k:A×B).2)⁻¹
      simp
  exact (congrArg (fun z : (subdirectSecond K).ker => χ.1 (Additive.ofMul z)) he).trans h

theorem subdirectRelativeCharacterMap_injective (K : Subgroup (A×B))
    (hA : Function.Surjective (Prod.fst ∘ K.subtype)) :
    Function.Injective (subdirectRelativeCharacterMap p K hA) := by
  intro χ ψ h
  apply Subtype.ext
  apply primeCharacterInflation_injective p (subdirectKernelEquiv K).symm.toMonoidHom
    (subdirectKernelEquiv K).symm.surjective
  simpa only [subdirectRelativeCharacterMap,primeCharacterInflation] using congrArg Subtype.val h

/-- Retained extendible axis characters of the original pair core. -/
def subdirectRetainedCharacters (K : Subgroup (A×B))
    (hA : Function.Surjective (Prod.fst ∘ K.subtype)) :
    letI := Subgroup.normal_goursatFst hA
    Submodule (ZMod p) (primeRelativeCharacters p K.goursatFst) :=
  LinearMap.range ((subdirectRelativeCharacterMap p K hA).comp
    (primeCharacterRestriction p (subdirectSecond K).ker))

/-- The exact rank identity keeps the actual extendibility cut even for
nonabelian proper subdirect pair cores. -/
theorem primeCharacterRank_subdirect_eq [Finite A] [Finite B]
    (K : Subgroup (A×B))
    (hA : Function.Surjective (Prod.fst ∘ K.subtype))
    (hB : Function.Surjective (Prod.snd ∘ K.subtype)) :
    Module.finrank (ZMod p) (PrimeCharacters p K) =
      Module.finrank (ZMod p) (PrimeCharacters p B) +
        Module.finrank (ZMod p) (subdirectRetainedCharacters p K hA) := by
  letI := Subgroup.normal_goursatFst hA
  let r := (subdirectRelativeCharacterMap p K hA).comp
    (primeCharacterRestriction p (subdirectSecond K).ker)
  have hk : LinearMap.ker r = LinearMap.ker (primeCharacterRestriction p (subdirectSecond K).ker) := by
    ext χ
    simp only [LinearMap.mem_ker,r,LinearMap.comp_apply]
    exact (subdirectRelativeCharacterMap_injective p K hA).eq_iff' (map_zero _) 
  have h := r.finrank_range_add_finrank_ker
  rw [hk,primeCharacterRestriction_ker p (subdirectSecond K) hB,
    LinearMap.finrank_range_of_inj (primeCharacterInflation_injective p (subdirectSecond K) hB)] at h
  exact h.symm.trans (Nat.add_comm _ _)

/-- Relative-head decomposition of an arbitrary full pair core.
The second term is the head of the actual axis under A, not the absolute
rank of the whole first image or the head under a smaller acting group. -/
theorem primeCharacterRank_subdirect_le [Finite A] [Finite B]
    (K : Subgroup (A×B))
    (hA : Function.Surjective (Prod.fst ∘ K.subtype))
    (hB : Function.Surjective (Prod.snd ∘ K.subtype)) :
    letI := Subgroup.normal_goursatFst hA
    Module.finrank (ZMod p) (PrimeCharacters p K) ≤
      Module.finrank (ZMod p) (PrimeCharacters p B) +
        Module.finrank (ZMod p) (primeRelativeCharacters p K.goursatFst) := by
  letI := Subgroup.normal_goursatFst hA
  have h := primeCharacterRank_extension_le p (subdirectSecond K) hB
  have hdim := (subdirectRelativeCharacterMap p K hA).finrank_le_finrank_of_injective
    (subdirectRelativeCharacterMap_injective p K hA)
  exact h.trans (Nat.add_le_add_left hdim _)

end SymmetricSubgroupAsymptotics
