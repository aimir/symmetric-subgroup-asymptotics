import SymmetricSubgroupAsymptotics.Non2LiftBound
import Mathlib.RepresentationTheory.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Quotient an actual original abelian kernel by an actual stable
submodule. The resulting chart is over the literal quotient homomorphism
Q/N -> B, retaining reconstruction and conjugation. No extension splitting,
finiteness, centrality of N, or cocycle-count hypothesis is assumed.

The arbitrary-normal-subgroup interface matches fixed-kernel subgroup
fibres directly. The original image of a stable submodule is also supplied,
with its exact membership condition and normality proved from the chart.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.OriginalKernelQuotientChart

universe u
variable {k Q B : Type u} [CommRing k] [Group Q] [Group B]

/-- The literal original group image of the selected module vectors. -/
def submoduleHom (π : Q →* B) (A : Rep k B) (E : OriginalKernelModuleChart π A)
    (K : Submodule k A) : Multiplicative K →* Q where
  toFun a := (E.equiv (Multiplicative.ofAdd a.toAdd.val) : Q)
  map_one' := by
    change (E.equiv 1 : Q)=1
    simp only [map_one,OneMemClass.coe_one]
  map_mul' a b := originalKernelChart_add π A E a.toAdd.val b.toAdd.val

theorem submoduleHom_injective (π : Q →* B) (A : Rep k B)
    (E : OriginalKernelModuleChart π A) (K : Submodule k A) :
    Function.Injective (submoduleHom π A E K) := by
  intro a b h
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact congrArg Multiplicative.toAdd (E.equiv.injective (Subtype.ext h))

def submoduleGroup (π : Q →* B) (A : Rep k B) (E : OriginalKernelModuleChart π A)
    (K : Submodule k A) : Subgroup Q := (submoduleHom π A E K).range

theorem chart_mem_submoduleGroup (π : Q →* B) (A : Rep k B)
    (E : OriginalKernelModuleChart π A) (K : Submodule k A) (a : Multiplicative A) :
    (E.equiv a : Q)∈submoduleGroup π A E K ↔ a.toAdd∈K := by
  constructor
  · rintro ⟨v,hv⟩
    have he : Multiplicative.ofAdd v.toAdd.val=a := E.equiv.injective (Subtype.ext hv)
    exact (congrArg Multiplicative.toAdd he) ▸ v.toAdd.property
  · intro ha
    exact ⟨Multiplicative.ofAdd ⟨a.toAdd,ha⟩,rfl⟩

theorem submoduleGroup_le_kernel (π : Q →* B) (A : Rep k B)
    (E : OriginalKernelModuleChart π A) (K : Submodule k A) :
    submoduleGroup π A E K≤π.ker := by
  rintro _ ⟨a,rfl⟩
  exact (E.equiv (Multiplicative.ofAdd a.toAdd.val)).property

/-- Stability under the actual quotient action proves normality in the
original Q; the selected vectors need not be fixed or central. -/
theorem submoduleGroup_normal (π : Q →* B) (A : Rep k B)
    (E : OriginalKernelModuleChart π A) (K : Submodule k A)
    (hK : ∀ b, K≤K.comap (A.ρ b)) : (submoduleGroup π A E K).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨a,rfl⟩ q
  refine ⟨Multiplicative.ofAdd ⟨A.ρ (π q) a.toAdd.val,
    hK (π q) a.toAdd.property⟩,?_⟩
  exact E.conjugate q a.toAdd.val

/-- Precisely the original quotient representation A/K. -/
def quotientModule (A : Rep k B) (K : Submodule k A)
    (hK : ∀ b, K≤K.comap (A.ρ b)) : Rep k B := Rep.of (A.ρ.quotient K hK)

def moduleProjection (A : Rep k B) (K : Submodule k A)
    (hK : ∀ b, K≤K.comap (A.ρ b)) :
    Multiplicative A →* Multiplicative (quotientModule A K hK) :=
  K.mkQ.toAddMonoidHom.toMultiplicative

theorem moduleProjection_surjective (A : Rep k B) (K : Submodule k A)
    (hK : ∀ b, K≤K.comap (A.ρ b)) : Function.Surjective (moduleProjection A K hK) := by
  intro a
  obtain ⟨v,hv⟩ := K.mkQ_surjective a.toAdd
  exact ⟨Multiplicative.ofAdd v,congrArg Multiplicative.ofAdd hv⟩

def kernelProjection (π : Q →* B) (A : Rep k B) (E : OriginalKernelModuleChart π A)
    (N : Subgroup Q) [N.Normal] (hN : N≤π.ker) :
    Multiplicative A →* (QuotientGroup.lift N π hN).ker where
  toFun a := ⟨QuotientGroup.mk' N (E.equiv a : Q), by
    change π (E.equiv a : Q)=1
    exact (E.equiv a).property⟩
  map_one' := by
    apply Subtype.ext
    simp only [map_one,OneMemClass.coe_one]
  map_mul' a b := by
    apply Subtype.ext
    change QuotientGroup.mk' N (E.equiv (a*b) : Q)=_
    simp only [map_mul,Subgroup.coe_mul]

theorem kernelProjection_surjective (π : Q →* B) (A : Rep k B)
    (E : OriginalKernelModuleChart π A) (N : Subgroup Q) [N.Normal] (hN : N≤π.ker) :
    Function.Surjective (kernelProjection π A E N hN) := by
  intro r
  obtain ⟨q,hq⟩ := QuotientGroup.mk'_surjective N r.val
  have hqK : q∈π.ker := by
    change π q=1
    change (QuotientGroup.lift N π hN) (QuotientGroup.mk' N q)=1
    rw [hq]
    exact r.property
  refine ⟨E.equiv.symm ⟨q,hqK⟩,?_⟩
  apply Subtype.ext
  change QuotientGroup.mk' N (E.equiv (E.equiv.symm ⟨q,hqK⟩) : Q)=r.val
  rw [MulEquiv.apply_symm_apply]
  exact hq

theorem projection_kernels_eq (π : Q →* B) (A : Rep k B)
    (E : OriginalKernelModuleChart π A) (K : Submodule k A)
    (hK : ∀ b, K≤K.comap (A.ρ b))
    (N : Subgroup Q) [N.Normal] (hN : N≤π.ker)
    (hKN : ∀ a : Multiplicative A, (E.equiv a : Q)∈N ↔ a.toAdd∈K) :
    (moduleProjection A K hK).ker=(kernelProjection π A E N hN).ker := by
  ext a
  change moduleProjection A K hK a=1 ↔ kernelProjection π A E N hN a=1
  rw [Subtype.ext_iff]
  change K.mkQ a.toAdd=0 ↔ QuotientGroup.mk' N (E.equiv a : Q)=1
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  exact (hKN a).symm.trans (QuotientGroup.eq_one_iff _).symm

def kernelEquiv (π : Q →* B) (A : Rep k B)
    (E : OriginalKernelModuleChart π A) (K : Submodule k A)
    (hK : ∀ b, K≤K.comap (A.ρ b))
    (N : Subgroup Q) [N.Normal] (hN : N≤π.ker)
    (hKN : ∀ a : Multiplicative A, (E.equiv a : Q)∈N ↔ a.toAdd∈K) :
    Multiplicative (quotientModule A K hK) ≃* (QuotientGroup.lift N π hN).ker :=
  (QuotientGroup.liftEquiv (moduleProjection A K hK).ker
    (moduleProjection_surjective A K hK) rfl).symm.trans
    (QuotientGroup.liftEquiv (moduleProjection A K hK).ker
      (kernelProjection_surjective π A E N hN)
      (projection_kernels_eq π A E K hK N hN hKN))

@[simp] theorem kernelEquiv_projection (π : Q →* B) (A : Rep k B)
    (E : OriginalKernelModuleChart π A) (K : Submodule k A)
    (hK : ∀ b, K≤K.comap (A.ρ b))
    (N : Subgroup Q) [N.Normal] (hN : N≤π.ker)
    (hKN : ∀ a : Multiplicative A, (E.equiv a : Q)∈N ↔ a.toAdd∈K)
    (a : Multiplicative A) :
    kernelEquiv π A E K hK N hN hKN (moduleProjection A K hK a)=
      kernelProjection π A E N hN a := by
  change (QuotientGroup.liftEquiv (moduleProjection A K hK).ker
    (kernelProjection_surjective π A E N hN)
    (projection_kernels_eq π A E K hK N hN hKN))
      ((QuotientGroup.liftEquiv (moduleProjection A K hK).ker
        (moduleProjection_surjective A K hK) rfl).symm (moduleProjection A K hK a))=_
  rw [← QuotientGroup.liftEquiv_mk (moduleProjection A K hK).ker
    (moduleProjection_surjective A K hK) rfl a,MulEquiv.symm_apply_apply]
  rfl

/-- The exact original quotient-kernel chart. Conjugation is proved by
lifting actual quotient elements and actual module vectors, then using
the original chart equation before applying the quotient homomorphism. -/
def quotientChart (π : Q →* B) (A : Rep k B)
    (E : OriginalKernelModuleChart π A) (K : Submodule k A)
    (hK : ∀ b, K≤K.comap (A.ρ b))
    (N : Subgroup Q) [N.Normal] (hN : N≤π.ker)
    (hKN : ∀ a : Multiplicative A, (E.equiv a : Q)∈N ↔ a.toAdd∈K) :
    OriginalKernelModuleChart (QuotientGroup.lift N π hN) (quotientModule A K hK) where
  equiv := kernelEquiv π A E K hK N hN hKN
  conjugate r a := by
    obtain ⟨q,rfl⟩ := QuotientGroup.mk'_surjective N r
    obtain ⟨v,rfl⟩ := K.mkQ_surjective a
    have he (v : A) :
        (kernelEquiv π A E K hK N hN hKN (moduleProjection A K hK (Multiplicative.ofAdd v)) :
          Q ⧸ N)=QuotientGroup.mk' N (E.equiv (Multiplicative.ofAdd v) : Q) :=
      congrArg Subtype.val (kernelEquiv_projection π A E K hK N hN hKN _)
    change (kernelEquiv π A E K hK N hN hKN
      (moduleProjection A K hK (Multiplicative.ofAdd (A.ρ (π q) v))) : Q ⧸ N)=_
    rw [he]
    have hv := he v
    change (kernelEquiv π A E K hK N hN hKN (Multiplicative.ofAdd (K.mkQ v)) :
      Q ⧸ N)=_ at hv
    rw [hv,E.conjugate,map_mul,map_mul,map_inv]

end SymmetricSubgroupAsymptotics.OriginalKernelQuotientChart
