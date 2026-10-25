import SymmetricSubgroupAsymptotics.ElementarySylowEightOrdinaryCFSGReduction

/-! Transport the elementary-Sylow eight-point theorem through the
literal faithful action. The exceptional primitive sporadic action is an
actual point relabeling of this source, not an unrelated failed action.
No rank-four action is mislabeled as a failed half-degree witness. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ElementarySylowEightFaithfulActionOrdinary

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X]

def relabelHom (e : X ≃ Fin 8) : G →* Equiv.Perm (Fin 8) :=
  e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G X)

structure ActualSporadicObstruction where
  points : X ≃ Fin 8
  sylow : Sylow 2 (relabelHom (G := G) points).range
  obstruction : ElementarySylowEightOrdinaryCFSGReduction.PrimitiveSporadicObstruction
    (relabelHom (G := G) points).range sylow

variable [MulAction.IsPretransitive G X]

theorem genRank_le_three_or_actual_sporadic (hCFSG : CFSG.CFSGClassification)
    (P : Sylow 2 G) (hel : ∀ g : P, g^2 = 1) (hcard : Nat.card X = 8) :
    MarkedC4.genRank G ≤ 3 ∨ Nonempty (ActualSporadicObstruction (G := G) (X := X)) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : X ≃ Fin 8 := Finite.equivFinOfCardEq hcard
  let rho := relabelHom (G := G) e
  have hrho : Function.Injective rho :=
    e.permCongrHom.injective.comp MulAction.toPerm_injective
  let f : G ≃* rho.range := MonoidHom.ofInjective hrho
  let R : Sylow 2 rho.range := P.mapSurjective (f := f.toMonoidHom) f.surjective
  have hR : ∀ r : R, r^2 = 1 := by
    intro r
    have hr : (r : rho.range) ∈ (P : Subgroup G).map f.toMonoidHom := r.property
    obtain ⟨g,hg,hgr⟩ := hr
    have hg2 : g^2 = 1 := congrArg (fun z : P => (z : G)) (hel ⟨g,hg⟩)
    apply Subtype.ext
    change (r : rho.range)^2 = 1
    rw [←hgr,←map_pow,hg2,map_one]
  letI : MulAction.IsPretransitive rho.range (Fin 8) := by
    constructor
    intro i j
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G (e.symm i) (e.symm j)
    refine ⟨rho.rangeRestrict g,?_⟩
    change e (g • e.symm i) = j
    simpa only [Equiv.apply_symm_apply] using congrArg e hg
  rcases ElementarySylowEightOrdinaryCFSGReduction.genRank_le_three_or_actual_sporadic
    rho.range hCFSG R hR with hh | hbad
  · exact Or.inl (by
      simpa only [←CoprimeNilpotentProductGenerators.genRank_mulEquiv f] using hh)
  · obtain ⟨w⟩ := hbad
    exact Or.inr ⟨⟨e,R,w⟩⟩

end SymmetricSubgroupAsymptotics.ElementarySylowEightFaithfulActionOrdinary
