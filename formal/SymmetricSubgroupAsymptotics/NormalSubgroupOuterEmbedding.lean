import SymmetricSubgroupAsymptotics.SimpleProductOuterWreath
import SymmetricSubgroupAsymptotics.FullSocleSelfCentralizing

/-! An actual self-centralizing normal simple power gives a faithful
outer-wreath action of the original ambient quotient. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.NormalSubgroupOuterEmbedding
open PrimitiveSocleRawStructure SimpleProductOuterWreath

def autCongr {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    MulAut A ≃* MulAut B where
  toFun a := e.symm.trans (a.trans e)
  invFun b := e.trans (b.trans e.symm)
  left_inv a := by ext x; simp only [MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]
  right_inv a := by ext x; simp only [MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]
  map_mul' a b := by ext x; simp only [MulEquiv.trans_apply,
    MulAut.mul_apply, MulEquiv.symm_apply_apply]

@[simp] theorem autCongr_apply {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (a : MulAut A) (x : B) :
    autCongr e a x = e (a (e.symm x)) := rfl

theorem autCongr_conj {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (a : A) :
    autCongr e (MulAut.conj a) = MulAut.conj (e a) := by
  ext x
  simp only [autCongr_apply, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

variable {G : Type} [Group G] (S : Subgroup G) [S.Normal]

theorem conjNormal_injective (hC : Subgroup.centralizer (S : Set G) = ⊥) :
    Function.Injective (MulAut.conjNormal (H := S) : G →* MulAut S) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro g hg
  have hm : g ∈ Subgroup.centralizer (S : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro s hs
    have he := congrArg (fun a : MulAut S => ((a ⟨s, hs⟩ : S) : G)) hg
    change g * s * g⁻¹ = s at he
    have hmul := congrArg (fun x : G => x * g) he
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmul.symm
  rwa [hC] at hm

variable {I T : Type} [Fintype I] [Group T] [Finite T] [IsSimpleGroup T]
    (hT : IsCenterless T) (e : S ≃* (I → T))

def outerAction : G →* OuterWreath T I :=
  (automorphismOuter hT).comp
    ((autCongr e).toMonoidHom.comp (MulAut.conjNormal (H := S)))

theorem outerAction_ker
    (hC : Subgroup.centralizer (S : Set G) = ⊥) :
    (outerAction S hT e).ker = S := by
  have hinj := conjNormal_injective S hC
  apply le_antisymm
  · intro g hg
    have hm : autCongr e (MulAut.conjNormal (H := S) g) ∈
        PrimitiveSocleRawStructure.Inner (I → T) := by
      rw [← automorphismOuter_ker hT]
      exact hg
    obtain ⟨x, hx⟩ := hm
    have hsame : MulAut.conjNormal (H := S) g =
        MulAut.conjNormal (H := S) (e.symm x : G) := by
      apply (autCongr e).injective
      rw [MulAut.conjNormal_val, autCongr_conj, e.apply_symm_apply]
      exact hx.symm
    exact (hinj hsame).symm ▸ (e.symm x).property
  · intro g hg
    change automorphismOuter hT (autCongr e (MulAut.conjNormal (H := S) g)) = 1
    have he : MulAut.conjNormal (H := S) g = MulAut.conj (⟨g, hg⟩ : S) :=
      MulAut.conjNormal_val (h := (⟨g, hg⟩ : S))
    rw [he, autCongr_conj]
    exact (show MulAut.conj (e ⟨g, hg⟩) ∈
        (automorphismOuter (I := I) hT).ker from by
      rw [automorphismOuter_ker]
      exact ⟨e ⟨g, hg⟩, rfl⟩)

def quotientEmbedding : (G ⧸ S) →* OuterWreath T I :=
  QuotientGroup.lift S (outerAction S hT e) (fun g hg =>
    (show g ∈ (outerAction S hT e).ker from by
      change automorphismOuter hT (autCongr e (MulAut.conjNormal (H := S) g)) = 1
      rw [show MulAut.conjNormal (H := S) g = MulAut.conj (⟨g, hg⟩ : S) from
        MulAut.conjNormal_val (h := (⟨g, hg⟩ : S)), autCongr_conj]
      rw [← MonoidHom.mem_ker, automorphismOuter_ker]
      exact ⟨e ⟨g, hg⟩, rfl⟩))

theorem quotientEmbedding_injective
    (hC : Subgroup.centralizer (S : Set G) = ⊥) :
    Function.Injective (quotientEmbedding S hT e) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro q
  induction q using QuotientGroup.induction_on with
  | H g =>
    intro hg
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [← outerAction_ker S hT e hC]
    exact hg

end SymmetricSubgroupAsymptotics.NormalSubgroupOuterEmbedding
