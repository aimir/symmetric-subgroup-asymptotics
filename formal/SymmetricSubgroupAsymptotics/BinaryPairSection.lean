import SymmetricSubgroupAsymptotics.BinaryPairFrames
import SymmetricSubgroupAsymptotics.BinaryPairRepresentation

/-! The exact section attached to an original physical pair frame and
an original normal subgroup. Its chart, kernel, acting quotient and
specified central cut are constructed from those original objects. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame

variable {X I : Type*} {U : Subgroup (Equiv.Perm X)}
variable (F : BinaryPairFrame U I) (N : Subgroup U)

/-- Image of the literal intersection N∩ker(top), with all its original
flip correlations retained. -/
def normalSpace : Submodule (ZMod 2) F.kernelSpace :=
  ((AddMonoidHom.toMultiplicativeRight.symm F.kernelSpaceHom).comp
    (N.subgroupOf F.top.ker).subtype.toAdditive).range.toZModSubmodule 2

def sectionMap : F.top.ker →* Multiplicative (F.kernelSpace ⧸ F.normalSpace N) :=
  (F.normalSpace N).mkQ.toAddMonoidHom.toMultiplicative.comp F.kernelSpaceHom

theorem sectionMap_surjective : Function.Surjective (F.sectionMap N) := by
  intro v
  obtain ⟨x,hx⟩ := (F.normalSpace N).mkQ_surjective v.toAdd
  obtain ⟨k,hk⟩ := F.kernelSpaceHom_bijective.2 (Multiplicative.ofAdd x)
  refine ⟨k,?_⟩
  change Multiplicative.ofAdd ((F.normalSpace N).mkQ (F.kernelSpaceHom k).toAdd)=v
  rw [hk]
  exact congrArg Multiplicative.ofAdd hx

/-- The chart kernel is the original intersection, not an isomorphic
normal subgroup chosen from a table. -/
theorem sectionMap_ker : (F.sectionMap N).ker=N.subgroupOf F.top.ker := by
  ext k
  change (F.normalSpace N).mkQ (F.kernelSpaceHom k).toAdd=0 ↔ (k:U)∈N
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨n,hn⟩
    have he : F.kernelSpaceHom (n.toMul:F.top.ker)=F.kernelSpaceHom k :=
      congrArg Multiplicative.ofAdd hn
    have hnk := F.kernelSpaceHom_bijective.1 he
    exact hnk ▸ n.toMul.property
  · intro hk
    exact ⟨Additive.ofMul (⟨k,hk⟩:N.subgroupOf F.top.ker),rfl⟩

variable [N.Normal]

/-- Conjugation on the exact quotient K/(K∩N), with the original
U/(K∨N) as acting top. -/
def sectionRepresentation : Representation (ZMod 2) (U ⧸ (F.top.ker⊔N))
    (F.kernelSpace ⧸ F.normalSpace N) :=
  normalSectionTopRepresentation F.top.ker N (F.sectionMap N)
    (F.sectionMap_surjective N) (F.sectionMap_ker N)

@[simp] theorem sectionRepresentation_apply (g : U) (k : F.top.ker) :
    F.sectionRepresentation N (QuotientGroup.mk' (F.top.ker⊔N) g)
      (F.sectionMap N k).toAdd =
        (F.sectionMap N (MulAut.conjNormal g k)).toAdd :=
  normalSectionTopRepresentation_apply F.top.ker N (F.sectionMap N)
    (F.sectionMap_surjective N) (F.sectionMap_ker N) g k

/-- A literal central cut inside this exact section. -/
def cutRepresentation (C : Submodule (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N))
    (hC : C≤(F.sectionRepresentation N).invariants) :
    Representation (ZMod 2) (U ⧸ (F.top.ker⊔N))
      ((F.kernelSpace ⧸ F.normalSpace N) ⧸ C) :=
  normalSectionCutRepresentation F.top.ker N (F.sectionMap N)
    (F.sectionMap_surjective N) (F.sectionMap_ker N) C hC

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
