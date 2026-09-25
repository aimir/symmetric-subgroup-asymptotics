import SymmetricSubgroupAsymptotics.ImprimitiveBlockEvaluation
import SymmetricSubgroupAsymptotics.ChiefConjugateIntersections

/-! Original local-chief coordinates and their actual stabilizer
conjugation law. The local series creates the actual ambient-normal
intersection chain, with its bottom and top proved from the block action. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics
section Coordinate
variable {A R : Type} [Group A] [Group R]
variable (N : Subgroup A) [N.Normal] (θ : N→*R) (L : Subgroup R)

def localChiefIntersectionCoordinate : localChiefIntersection N θ L→*L where
  toFun c := ⟨θ ⟨c,localChiefIntersection_le N θ L c.2⟩,by
    have h := (mem_localChiefIntersection N θ L
      ⟨c,localChiefIntersection_le N θ L c.2⟩).mp c.2 1
    simpa only [map_one,MulAut.one_apply] using h⟩
  map_one' := Subtype.ext θ.map_one
  map_mul' c d := by
    apply Subtype.ext
    exact θ.map_mul ⟨(c:A),localChiefIntersection_le N θ L c.2⟩
      ⟨(d:A),localChiefIntersection_le N θ L d.2⟩

theorem localChiefIntersectionCoordinate_apply (c:localChiefIntersection N θ L) :
    (localChiefIntersectionCoordinate N θ L c:R)=
      θ ⟨c,localChiefIntersection_le N θ L c.2⟩ := rfl

end Coordinate
section Block
variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
variable (b : Ω→X) (hb : ∀ (a:A) (ω:Ω),b (a•ω)=a•b ω) (x₀:X)
variable (N : Subgroup A) [N.Normal] (hN : N≤(MulAction.toPermHom A X).ker)

def originalBlockProjection : MulAction.stabilizer A x₀→* originalBlockComponent b hb x₀ :=
  (originalBlockFibreAction b hb x₀).rangeRestrict

theorem originalBlockEvaluation_conjugation (h:MulAction.stabilizer A x₀) (n:N) :
    originalBlockEvaluation b hb x₀ N hN (MulAut.conjNormal (h:A) n)=
      originalBlockProjection b hb x₀ h*
        originalBlockEvaluation b hb x₀ N hN n*
          (originalBlockProjection b hb x₀ h)⁻¹ := by
  have hc : blockKernelToStabilizer x₀ N hN (MulAut.conjNormal (h:A) n)=
      h*blockKernelToStabilizer x₀ N hN n*h⁻¹ := by
    apply Subtype.ext
    rfl
  change originalBlockProjection b hb x₀
    (blockKernelToStabilizer x₀ N hN (MulAut.conjNormal (h:A) n))=_
  rw [hc,map_mul,map_mul,map_inv]
  rfl

abbrev originalBlockChiefIntersection
    (L : Subgroup (originalBlockComponent b hb x₀)) : Subgroup A :=
  localChiefIntersection N (originalBlockEvaluation b hb x₀ N hN) L

theorem originalBlockChiefIntersection_top :
    originalBlockChiefIntersection b hb x₀ N hN ⊤=N :=
  localChiefIntersection_top N (originalBlockEvaluation b hb x₀ N hN)

theorem originalBlockChiefIntersection_bot [FaithfulSMul A Ω] [MulAction.IsPretransitive A X] :
    originalBlockChiefIntersection b hb x₀ N hN ⊥=⊥ :=
  localChiefIntersection_bot N (originalBlockEvaluation b hb x₀ N hN)
    (originalBlockEvaluation_conjugates_separate b hb x₀ N hN)

theorem originalBlockChiefIntersection_mono
    {L M : Subgroup (originalBlockComponent b hb x₀)} (hLM:L≤M) :
    originalBlockChiefIntersection b hb x₀ N hN L≤
      originalBlockChiefIntersection b hb x₀ N hN M :=
  localChiefIntersection_mono N (originalBlockEvaluation b hb x₀ N hN) hLM

end Block
end SymmetricSubgroupAsymptotics
