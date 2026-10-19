import SymmetricSubgroupAsymptotics.AbelianProductGraphClassification
import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers
import Mathlib.Data.SetLike.Fintype

/-! The actual isolated-free fibre used after graph-first normalization.
For an arbitrary nonabelian physical first factor, a second-full subgroup
with trivial isolated first intersection is the graph of an ACTUAL hom from
the retained second image. Its finite epimorphism cost is constructed here. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualIsolatedFreeFibre
open AbelianProductGraphClassification

variable (G E : Type) [Group G] [Group E]
abbrev Family := {J : FullSecond G E // ∀ g : G,(g,1)∈J.val → g=1}

def second (J : Family G E) : J.val.val →* E :=
  (MonoidHom.snd G E).comp J.val.val.subtype

theorem second_surjective (J : Family G E) : Function.Surjective (second G E J) := by
  intro e
  have he : e∈J.val.val.map (MonoidHom.snd G E) := by
    rw [J.val.property]
    trivial
  obtain ⟨x,hx,hxe⟩ := he
  exact ⟨⟨x,hx⟩,hxe⟩

theorem second_injective (J : Family G E) : Function.Injective (second G E J) := by
  apply (MonoidHom.ker_eq_bot_iff (second G E J)).mp
  apply le_antisymm _ bot_le
  intro x hx
  have hx2 : x.val.2=1 := MonoidHom.mem_ker.mp hx
  have hm : (x.val.1,1)∈J.val.val := by
    have he : (x.val.1,1)=x.val := Prod.ext rfl hx2.symm
    rw [he]
    exact x.property
  have hx1 := J.property x.val.1 hm
  apply Subgroup.mem_bot.mpr
  exact Subtype.ext (Prod.ext hx1 hx2)

def secondEquiv (J : Family G E) : J.val.val ≃* E :=
  MulEquiv.ofBijective (second G E J) ⟨second_injective G E J,second_surjective G E J⟩

def code (J : Family G E) : E →* G :=
  ((MonoidHom.fst G E).comp J.val.val.subtype).comp (secondEquiv G E J).symm.toMonoidHom

/-- Literal graph recovery in the original G×E ambient group. -/
theorem mem_iff (J : Family G E) (x : G × E) :
    x∈J.val.val ↔ code G E J x.2=x.1 := by
  constructor
  · intro hx
    have he := (secondEquiv G E J).symm_apply_apply ⟨x,hx⟩
    exact congrArg (fun z : J.val.val => z.val.1) he
  · intro hx
    let z := (secondEquiv G E J).symm x.2
    have hz : z.val=x := by
      apply Prod.ext hx
      exact (secondEquiv G E J).apply_symm_apply x.2
    exact hz ▸ z.property

theorem code_injective : Function.Injective (code G E) := by
  intro J K he
  apply Subtype.ext
  apply Subtype.ext
  ext x
  rw [mem_iff G E J,mem_iff G E K,he]

/-- An actual source generator set determines every homomorphism to the
actual physical target; no external generator-capacity field is accepted. -/
theorem hom_card_le [Finite E] [Finite G] :
    Nat.card (E →* G)≤Nat.card G^genRank E := by
  obtain ⟨S,hcard,hgen⟩ := genRank_spec (G := E)
  let ev : (E →* G) → (S → G) := fun f s => f s.val
  have hinj : Function.Injective ev := by
    intro f g he
    apply MonoidHom.eq_of_eqOn_dense hgen
    intro x hx
    exact congrFun he ⟨x,hx⟩
  calc
    _ ≤ Nat.card (S → G) := Nat.card_le_card_of_injective ev hinj
    _ = _ := by
      rw [Nat.card_fun,Nat.card_eq_fintype_card (α := S),Fintype.card_coe,hcard]

/-- Concrete finite Case-II fibre bound after isolated intersections have
been removed from the SAME global marked graph. -/
theorem card_le [Finite G] [Finite E] :
    Nat.card (Family G E)≤Nat.card G^genRank E := by
  letI : Finite (E →* G) := Finite.of_injective
    (fun f : E →* G => (f : E → G)) DFunLike.coe_injective
  exact (Nat.card_le_card_of_injective (code G E) (code_injective G E)).trans (hom_card_le G E)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualIsolatedFreeFibre
