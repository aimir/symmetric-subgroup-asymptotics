import SymmetricSubgroupAsymptotics.CFSGFFourBinaryFixedRadicalEmbedding

/-! Literal central/kernel coordinates for the same fixed F4 radical.
The seven central coordinates and the eight-dimensional quotient are
actual homomorphism data. These statements do not identify a Levi
representation or assume an orbit lower bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryRadicalCentralLayers
open CFSGHeisenbergCoordinateGroup CFSGFFourBinaryFixedRadicalEmbedding
variable (K : Type) [Field K]

abbrev CentralCoordinates := Multiplicative (K × Extra K)

def centralCoordinates : CentralCoordinates K →* Radical K where
  toFun c := (central (Multiplicative.ofAdd c.toAdd.1), Multiplicative.ofAdd c.toAdd.2)
  map_one' := rfl
  map_mul' c d := by
    apply Prod.ext
    · exact (central (K := K) (m := 4)).map_mul
        (Multiplicative.ofAdd c.toAdd.1) (Multiplicative.ofAdd d.toAdd.1)
    · rfl

theorem centralCoordinates_injective : Function.Injective (centralCoordinates K) := by
  intro c d he
  have hc : Multiplicative.ofAdd c.toAdd.1 = Multiplicative.ofAdd d.toAdd.1 :=
    central_injective (congrArg (fun z : Radical K => z.1) he)
  have hv : Multiplicative.ofAdd c.toAdd.2 = Multiplicative.ofAdd d.toAdd.2 :=
    congrArg (fun z : Radical K => z.2) he
  apply Multiplicative.toAdd.injective
  exact Prod.ext (congrArg (fun z : Multiplicative K => z.toAdd) hc)
    (congrArg (fun z : Multiplicative (Extra K) => z.toAdd) hv)

def vectorProjection : Radical K →* Multiplicative ((Fin 4 → K) × (Fin 4 → K)) :=
  (projection (K := K) (m := 4)).comp (MonoidHom.fst _ _)

theorem mem_vectorProjection_ker (g : Radical K) :
    g ∈ (vectorProjection K).ker ↔ g.1.a=0 ∧ g.1.b=0 :=
  mem_projection_ker g.1

theorem vectorProjection_ker : (vectorProjection K).ker = (centralCoordinates K).range := by
  apply Subgroup.ext
  intro g
  constructor
  · intro hg
    obtain ⟨ha,hb⟩ := (mem_vectorProjection_ker K g).mp hg
    refine ⟨Multiplicative.ofAdd (g.1.c,g.2.toAdd),?_⟩
    apply Prod.ext
    · exact Element.ext ha.symm hb.symm rfl
    · rfl
  · rintro ⟨c,rfl⟩
    exact (mem_vectorProjection_ker K _).mpr ⟨rfl,rfl⟩

theorem centralCoordinates_commute (c : CentralCoordinates K) (g : Radical K) :
    Commute (centralCoordinates K c) g := by
  change centralCoordinates K c*g = g*centralCoordinates K c
  apply Prod.ext
  · apply Element.ext
    · change 0+g.1.a = g.1.a+0
      simp only [zero_add,add_zero]
    · change 0+g.1.b = g.1.b+0
      simp only [zero_add,add_zero]
    · change c.toAdd.1+g.1.c+dot 0 g.1.a = g.1.c+c.toAdd.1+dot g.1.b 0
      simp only [dot,Pi.zero_apply,zero_mul,mul_zero,Finset.sum_const_zero,add_zero]
      exact add_comm _ _
  · exact mul_comm _ _

theorem centralCoordinates_card [Finite K] : Nat.card (CentralCoordinates K) = Nat.card K^7 := by
  rw [Nat.card_congr (Multiplicative.toAdd : CentralCoordinates K ≃ K × Extra K)]
  simp only [Extra,Nat.card_prod,Nat.card_fun,Nat.card_fin]
  ring

theorem radical_card [Finite K] : Nat.card (Radical K) = Nat.card K^15 := by
  have he : Nat.card (Multiplicative (Extra K)) = Nat.card K^6 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Extra K) ≃ Extra K)]
    simp only [Extra,Nat.card_prod,Nat.card_fun,Nat.card_fin]
    ring
  rw [Nat.card_prod,CFSGHeisenbergCoordinateGroup.card,he]
  ring

variable [Finite K] [CharP K 2]
  [IsSimpleGroup (CFSG.Models.Chevalley.Projective CartanMatrix.F₄ K)]

def originalCentralHom : CentralCoordinates K →*
    CFSG.Models.Chevalley.Projective CartanMatrix.F₄ K :=
  (originalHom K).comp (centralCoordinates K)

theorem originalCentralHom_injective : Function.Injective (originalCentralHom K) :=
  (originalHom_injective K).comp (centralCoordinates_injective K)

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryRadicalCentralLayers
