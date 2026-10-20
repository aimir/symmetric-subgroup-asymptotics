import SymmetricSubgroupAsymptotics.MarkedC4ActualIsolatedFreeFibre

/-! The actual isolated-free subdirect fibre injects into epimorphisms.
This is the exact Goursat input for arbitrary-normal-F RDT Theorem 4.6,
retaining the actual residual group (including its one global mark). -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualIsolatedFreeEpimorphism

variable (G E : Type) [Group G] [Group E]
abbrev Family := {J : ActualIsolatedFreeFibre.Family G E //
  J.val.val.map (MonoidHom.fst G E)=⊤}

theorem code_surjective (J : Family G E) :
    Function.Surjective (ActualIsolatedFreeFibre.code G E J.val) := by
  intro g
  have hg : g∈J.val.val.val.map (MonoidHom.fst G E) := by
    rw [J.property]
    trivial
  obtain ⟨x,hx,hxg⟩ := hg
  exact ⟨x.2,((ActualIsolatedFreeFibre.mem_iff G E J.val x).mp hx).trans hxg⟩

def code (J : Family G E) : {f : E →* G // Function.Surjective f} :=
  ⟨ActualIsolatedFreeFibre.code G E J.val,code_surjective G E J⟩

theorem code_injective : Function.Injective (code G E) := by
  intro J K he
  apply Subtype.ext
  exact ActualIsolatedFreeFibre.code_injective G E (congrArg Subtype.val he)

theorem card_le [Finite G] [Finite E] :
    Nat.card (Family G E)≤Nat.card {f : E →* G // Function.Surjective f} := by
  letI : Finite (E →* G) := Finite.of_injective
    (fun f : E →* G => (f : E → G)) DFunLike.coe_injective
  exact Nat.card_le_card_of_injective (code G E) (code_injective G E)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualIsolatedFreeEpimorphism
