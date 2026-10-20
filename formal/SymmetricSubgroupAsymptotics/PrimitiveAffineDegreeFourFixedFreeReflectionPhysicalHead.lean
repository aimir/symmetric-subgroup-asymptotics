import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourOriginalCubicReflectionLift
import SymmetricSubgroupAsymptotics.PrimitiveAffineOriginalCubicReflectionFixedFibreChart
import SymmetricSubgroupAsymptotics.PrimitiveAffineOriginalReflectionMovingFibreChart
import SymmetricSubgroupAsymptotics.PrimitiveAffineOriginalTranslationCoordinateIdentity
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourOriginalLocalFaithfulnessEveryBlock
import SymmetricSubgroupAsymptotics.BinaryFourCubicNormalizerShapeHead
import SymmetricSubgroupAsymptotics.BinaryFourCubicFibreTransportGauge

/-! The negative fixed-translation S4 branch on the unchanged sixteen
physical points. The actual odd lift and both physical fibre charts are
constructed before applying the four-orbit coinduced bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinaryFourBlockAugmentation BinaryFourCubicNormalizerPointShapes
variable {U : PreE7NonPairActionClass 16} {basePoint : Fin 16}
    (block : OriginalMinimalBlock (A := preE7NonPairAction 16 U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]

private def labelFibre (d : block.Points ≃ Fin 4) (j : Fin 4) :
    originalBlockFibre block.map (d.symm j) ≃
      {x : Fin 16 // d (block.map x) = j} :=
  Equiv.subtypeEquivRight (fun x => by
    constructor
    · intro h
      rw [h,d.apply_symm_apply]
    · intro h
      apply d.injective
      exact h.trans (d.apply_symm_apply j).symm)

namespace DegreeFourS4OriginalPointChart

theorem fixedFreeTranslation_physical_head
    (C : DegreeFourS4OriginalPointChart block)
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (S : Sylow 3 (preE7NonPairAction 16 U)) (s : preE7NonPairAction 16 U)
    (d : block.Points ≃ Fin 4)
    (hgen : (S : Subgroup (preE7NonPairAction 16 U)) = Subgroup.zpowers s)
    (hs3 : s^3 = 1) (hsq : QuotientGroup.mk' (E block P) s ≠ 1)
    (hd : ∀ i : block.Points, d (s • i) = blockCycle (d i))
    (hzero : ∀ e : preE7NonPairAction 16 U, e ∈ E block P →
      (∀ t : preE7NonPairAction 16 U, t ∈ (S : Subgroup (preE7NonPairAction 16 U)) →
        e*t=t*e) → e=1)
    {L V : Type} [Group L] [Finite L] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (x : Fin 16) (f : MulAction.stabilizer (preE7NonPairAction 16 U) x →* L)
    (hf : Function.Surjective f) (rho : Representation (ZMod 2) L V)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer (preE7NonPairAction 16 U) x).subtype
        (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) (preE7NonPairAction 16 U) (ZMod 2))) ≤ 8 := by
  obtain ⟨g,hgn,hg2,hgs,hgd⟩ := originalCubicReflectionLift block P C hr hD
    S s d hgen hd hzero
  have hsi : s • d.symm 0 = d.symm 0 := by
    apply d.injective
    rw [hd,d.apply_symm_apply]
    decide +kernel
  have hgi (j : Fin 4) (hj : j=0 ∨ j=1) : g • d.symm j = d.symm j := by
    apply d.injective
    rw [hgd,d.apply_symm_apply]
    rcases hj with rfl | rfl <;> decide +kernel
  have hgq : QuotientGroup.mk' (E block P) g ≠ 1 := by
    intro h
    have he : g ∈ E block P := (QuotientGroup.eq_one_iff (N := E block P) g).mp h
    have hf := originalTranslation_fixes_blocks block P ⟨g,he⟩ (d.symm 2)
    have hh := hgd (d.symm 2)
    rw [hf,d.apply_symm_apply] at hh
    have hn : (2 : Fin 4) ≠ Equiv.swap 2 3 2 := by decide +kernel
    exact hn hh
  have hlocal0 := originalLocalMap_injective_at block P C hr hD (d.symm 0)
  obtain ⟨a,has,hag⟩ := originalCubicReflectionFixedFibreChart block P hr
    (d.symm 0) s g hsi (hgi 0 (Or.inl rfl)) hs3 hsq hg2 hgs hlocal0
  have hell : localMap block P ((ambientEmbedding block g).left (d.symm 1)) ≠ 1 := by
    intro h
    let q : binaryAffineQuotientTopStabilizer block P (d.symm 1) :=
      ⟨QuotientGroup.mk' (E block P) g,by change g • d.symm 1=d.symm 1; exact hgi 1 (Or.inr rfl)⟩
    have hq : binaryAffineStabilizerComponent block P (d.symm 1) q = 1 := h
    have hq1 : q=1 := originalLocalMap_injective_at block P C hr hD (d.symm 1)
      (hq.trans (binaryAffineStabilizerComponent block P (d.symm 1)).map_one.symm)
    exact hgq (congrArg Subtype.val hq1)
  obtain ⟨b,hbg⟩ := originalReflectionMovingFibreChart block P hr (d.symm 1)
    g (hgi 1 (Or.inr rfl)) hg2 hell
  let fixed := a.trans (labelFibre block d 0)
  let moving := b.trans (labelFibre block d 1)
  let pi : Fin 16 → Fin 4 := fun y => d (block.map y)
  have hpi (y : Fin 16) : pi (s • y)=blockCycle (pi y) := by
    change d (block.map (s • y))=blockCycle (d (block.map y))
    rw [block.map_equivariant,hd]
  have hinv : s⁻¹=s^2 := by
    calc
      s⁻¹ = s⁻¹*1 := (mul_one _).symm
      _ = s⁻¹*s^3 := by rw [hs3]
      _ = s^2 := by group
  have hrel : g*s=s^2*g := by
    have h := congrArg (fun t : preE7NonPairAction 16 U => t*g) hgs
    simpa only [mul_assoc,inv_mul_cancel,mul_one,hinv] using h
  have hconj2 : g*s^2*g⁻¹=s := by
    calc
      g*s^2*g⁻¹ = (g*s*g⁻¹)^2 :=
        map_pow (MulAut.conj g).toMonoidHom s 2
      _ = (s⁻¹)^2 := by rw [hgs]
      _ = s := by
        rw [hinv,←pow_mul]
        calc
          s^4=s^3*s := by group
          _=s := by rw [hs3,one_mul]
  have hrel2 : g*s^2=s*g := by
    have h := congrArg (fun t : preE7NonPairAction 16 U => t*g) hconj2
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using h
  have hflip (y : Fin 16) : g • (s • y)=s^2 • (g • y) := by
    simpa only [mul_smul] using congrArg
      (fun t : preE7NonPairAction 16 U => t • y) hrel
  have hflip2 (y : Fin 16) : g • (s^2 • y)=s • (g • y) := by
    simpa only [mul_smul] using congrArg
      (fun t : preE7NonPairAction 16 U => t • y) hrel2
  let F := BinaryFourCubicFibreTransportGauge.pointEquiv pi s fixed moving hpi (by simp)
  have hsF : F.symm.permCongrHom
      (MulAction.toPermHom (preE7NonPairAction 16 U) (Fin 16) s) =
        BinaryFourCubicNormalizerPointShapes.rotation := by
    apply Equiv.ext
    intro p
    apply F.injective
    change F (F.symm (s • F p))=F (BinaryFourCubicNormalizerPointShapes.rotation p)
    rw [F.apply_symm_apply]
    exact (BinaryFourCubicFibreTransportGauge.pointEquiv_rotation
      pi s fixed moving hpi (by simp) hs3 has p).symm
  have hgF : F.symm.permCongrHom
      (MulAction.toPermHom (preE7NonPairAction 16 U) (Fin 16) g) =
        BinaryFourCubicNormalizerPointShapes.reflection := by
    apply Equiv.ext
    intro p
    apply F.injective
    change F (F.symm (g • F p))=F (BinaryFourCubicNormalizerPointShapes.reflection p)
    rw [F.apply_symm_apply]
    exact (BinaryFourCubicFibreTransportGauge.pointEquiv_reflection
      pi s fixed moving hpi (by simp) g hflip hflip2 hag hbg p).symm
  exact BinaryFourCubicNormalizerShapeHead.reflection_head_le_eight F.symm S s g
    hgen hgn hsF hgF x f hf rho hL hdim hrho B

end DegreeFourS4OriginalPointChart
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
