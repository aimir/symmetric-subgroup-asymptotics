import SymmetricSubgroupAsymptotics.SchurPGroupCapacity
import Mathlib.Algebra.Module.ZMod
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! Actual normal-section representations for pair certificates.
The supplied chart is an onto map on the literal normal K with exact
kernel K∩N. Conjugation, the original top U/(K∨N), and equivariance of
the chart are then constructed, not postulated. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {p : ℕ} {U V : Type*} [Group U] [AddCommGroup V] [Module (ZMod p) V]
variable (K N : Subgroup U) [K.Normal] [N.Normal]
variable (q : K →* Multiplicative V) (hq : Function.Surjective q)
variable (hker : q.ker=N.subgroupOf K)

include hker in
private theorem normalSection_conj_ker (g : U) :
    q.ker ≤ (q.comp ((MulAut.conjNormal (H := K)) g).toMonoidHom).ker := by
  intro x hx
  apply MonoidHom.mem_ker.mpr
  change q (MulAut.conjNormal g x)=1
  apply MonoidHom.mem_ker.mp
  rw [hker] at hx ⊢
  change g*(x:U)*g⁻¹∈N
  change (x:U)∈N at hx
  exact Subgroup.Normal.conj_mem (H := N) inferInstance _ hx g

def normalSectionConjugateHom (g : U) : Multiplicative V →* Multiplicative V :=
  q.liftOfSurjective hq ⟨q.comp ((MulAut.conjNormal (H := K)) g).toMonoidHom,
    normalSection_conj_ker K N q hker g⟩

@[simp] theorem normalSectionConjugateHom_apply (g : U) (k : K) :
    normalSectionConjugateHom K N q hq hker g (q k)=q (MulAut.conjNormal g k) := by
  exact MonoidHom.liftOfRightInverse_comp_apply q (Function.surjInv hq)
    (Function.rightInverse_surjInv hq) _ k

def normalSectionLinearMap (g : U) : V →ₗ[ZMod p] V :=
  (AddMonoidHom.toMultiplicative.symm (normalSectionConjugateHom K N q hq hker g)).toZModLinearMap p

@[simp] theorem normalSectionLinearMap_apply (g : U) (k : K) :
    normalSectionLinearMap (p := p) K N q hq hker g (q k).toAdd =
      (q (MulAut.conjNormal g k)).toAdd := by
  exact congrArg Multiplicative.toAdd (normalSectionConjugateHom_apply K N q hq hker g k)

/-- Conjugation on the original section, in its exact supplied vector chart. -/
def normalSectionRepresentation : Representation (ZMod p) U V where
  toFun := normalSectionLinearMap (p := p) K N q hq hker
  map_one' := by
    apply LinearMap.ext
    intro v
    obtain ⟨k,hk⟩ := hq (Multiplicative.ofAdd v)
    have hv : (q k).toAdd=v := congrArg Multiplicative.toAdd hk
    rw [←hv,normalSectionLinearMap_apply]
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    obtain ⟨k,hk⟩ := hq (Multiplicative.ofAdd v)
    have hv : (q k).toAdd=v := congrArg Multiplicative.toAdd hk
    rw [←hv]
    change normalSectionLinearMap (p := p) K N q hq hker (g*h) (q k).toAdd =
      normalSectionLinearMap (p := p) K N q hq hker g
        (normalSectionLinearMap (p := p) K N q hq hker h (q k).toAdd)
    rw [normalSectionLinearMap_apply,normalSectionLinearMap_apply,normalSectionLinearMap_apply]
    rw [map_mul]
    rfl

@[simp] theorem normalSectionRepresentation_apply (g : U) (k : K) :
    normalSectionRepresentation (p := p) K N q hq hker g (q k).toAdd =
      (q (MulAut.conjNormal g k)).toAdd := normalSectionLinearMap_apply (p := p) K N q hq hker g k

theorem normalSectionRepresentation_trivial_K (g : K) (v : V) :
    normalSectionRepresentation (p := p) K N q hq hker (g:U) v=v := by
  obtain ⟨k,hk⟩ := hq (Multiplicative.ofAdd v)
  have hv : (q k).toAdd=v := congrArg Multiplicative.toAdd hk
  rw [←hv,normalSectionRepresentation_apply,MulAut.conjNormal_val]
  simp [MulAut.conj_apply]

theorem normalSectionRepresentation_trivial_N (g : N) (v : V) :
    normalSectionRepresentation (p := p) K N q hq hker (g:U) v=v := by
  obtain ⟨k,hk⟩ := hq (Multiplicative.ofAdd v)
  have hv : (q k).toAdd=v := congrArg Multiplicative.toAdd hk
  rw [←hv,normalSectionRepresentation_apply]
  apply congrArg Multiplicative.toAdd
  apply (MonoidHom.eq_iff q).mpr
  rw [hker]
  change (k:U)⁻¹*((g:U)*(k:U)*(g:U)⁻¹)∈N
  have hc : (k:U)⁻¹*(g:U)*(k:U)∈N := by
    simpa using Subgroup.Normal.conj_mem (H := N) inferInstance (g:U) g.2 (k:U)⁻¹
  simpa only [mul_assoc] using N.mul_mem hc (N.inv_mem g.2)

theorem normalSectionRepresentation_ker : K⊔N ≤ (normalSectionRepresentation (p := p) K N q hq hker).ker := by
  apply sup_le
  · intro g hg
    apply MonoidHom.mem_ker.mpr
    apply LinearMap.ext
    intro v
    exact normalSectionRepresentation_trivial_K (p := p) K N q hq hker ⟨g,hg⟩ v
  · intro g hg
    apply MonoidHom.mem_ker.mpr
    apply LinearMap.ext
    intro v
    exact normalSectionRepresentation_trivial_N (p := p) K N q hq hker ⟨g,hg⟩ v

/-- The acting top is the original literal quotient, not an abstract substitute. -/
def normalSectionTopRepresentation : Representation (ZMod p) (U ⧸ (K⊔N)) V :=
  QuotientGroup.lift (K⊔N) (normalSectionRepresentation (p := p) K N q hq hker)
    (normalSectionRepresentation_ker (p := p) K N q hq hker)

@[simp] theorem normalSectionTopRepresentation_apply (g : U) (k : K) :
    normalSectionTopRepresentation (p := p) K N q hq hker (QuotientGroup.mk' (K⊔N) g) (q k).toAdd =
      (q (MulAut.conjNormal g k)).toAdd :=
  normalSectionRepresentation_apply (p := p) K N q hq hker g k

/-- A specified central cut is a subspace of this same section's invariants. -/
def normalSectionCutRepresentation (C : Submodule (ZMod p) V)
    (hC : C≤(normalSectionTopRepresentation (p := p) K N q hq hker).invariants) :
    Representation (ZMod p) (U ⧸ (K⊔N)) (V ⧸ C) :=
  (normalSectionTopRepresentation (p := p) K N q hq hker).quotient C (fun g x hx => by
    change normalSectionTopRepresentation (p := p) K N q hq hker g x∈C
    rw [hC hx g]
    exact hx)

/-- The cut's map still starts on the literal K. -/
def normalSectionCutMap (C : Submodule (ZMod p) V) : K →* Multiplicative (V ⧸ C) :=
  C.mkQ.toAddMonoidHom.toMultiplicative.comp q

include hq in
omit [K.Normal] in
theorem normalSectionCutMap_surjective (C : Submodule (ZMod p) V) :
    Function.Surjective (normalSectionCutMap K q C) := by
  intro v
  obtain ⟨x,hx⟩ := C.mkQ_surjective v.toAdd
  obtain ⟨k,hk⟩ := hq (Multiplicative.ofAdd x)
  refine ⟨k,?_⟩
  change Multiplicative.ofAdd (C.mkQ (q k).toAdd)=v
  rw [hk]
  exact congrArg Multiplicative.ofAdd hx

omit [K.Normal] in
theorem normalSectionCutMap_ker (C : Submodule (ZMod p) V) (k : K) :
    k∈(normalSectionCutMap K q C).ker ↔ (q k).toAdd∈C := by
  change C.mkQ (q k).toAdd=0 ↔ _
  exact Submodule.Quotient.mk_eq_zero C

@[simp] theorem normalSectionCutRepresentation_apply (C : Submodule (ZMod p) V)
    (hC : C≤(normalSectionTopRepresentation (p := p) K N q hq hker).invariants)
    (g : U) (k : K) :
    normalSectionCutRepresentation K N q hq hker C hC (QuotientGroup.mk' (K⊔N) g)
      (normalSectionCutMap K q C k).toAdd =
        (normalSectionCutMap K q C (MulAut.conjNormal g k)).toAdd := by
  change C.mkQ (normalSectionTopRepresentation (p := p) K N q hq hker
    (QuotientGroup.mk' (K⊔N) g) (q k).toAdd)=_
  rw [normalSectionTopRepresentation_apply]
  rfl

end SymmetricSubgroupAsymptotics
