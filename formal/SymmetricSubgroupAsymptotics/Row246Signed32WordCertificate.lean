import SymmetricSubgroupAsymptotics.KleinParitySignedBinaryTop
import SymmetricSubgroupAsymptotics.FiniteGeneratorWord
import SymmetricSubgroupAsymptotics.TwoAxisAbelianizationCover
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row246Signed32WordCertificate
open KleinParitySignedBinaryTop
local instance : Inhabited (FiniteGeneratorWord (Fin 2)) := ⟨.one⟩
local instance : DecidableEq Full := fun g h =>
  decidable_of_iff (g.left=h.left ∧ g.right=h.right) (by
    constructor
    · rintro ⟨hl,hr⟩; exact SemidirectProduct.ext hl hr
    · intro he; exact ⟨congrArg SemidirectProduct.left he,congrArg SemidirectProduct.right he⟩)

def generators : Fin 2 → Group := ![X,Y]
def fullGenerators : Fin 2 → Full := ![x,y]
def states : Fin 32 → Full := fun i =>
  (#[raw (![0,0,0,0]) (Multiplicative.ofAdd 0,Multiplicative.ofAdd 0),
   raw (![0,0,0,0]) (Multiplicative.ofAdd 1,Multiplicative.ofAdd 0),
   raw (![1,0,0,0]) (Multiplicative.ofAdd 0,Multiplicative.ofAdd 1),
   raw (![1,0,0,0]) (Multiplicative.ofAdd 1,Multiplicative.ofAdd 1),
   raw (![0,1,0,0]) (Multiplicative.ofAdd 0,Multiplicative.ofAdd 1),
   raw (![0,1,0,0]) (Multiplicative.ofAdd 1,Multiplicative.ofAdd 1),
   raw (![1,1,0,0]) (Multiplicative.ofAdd 0,Multiplicative.ofAdd 0),
   raw (![1,1,0,0]) (Multiplicative.ofAdd 1,Multiplicative.ofAdd 0),
   raw (![0,0,1,0]) (Multiplicative.ofAdd 0,Multiplicative.ofAdd 1),
   raw (![0,0,1,0]) (Multiplicative.ofAdd 1,Multiplicative.ofAdd 1),
   raw (![1,0,1,0]) (Multiplicative.ofAdd 0,Multiplicative.ofAdd 0),
   raw (![1,0,1,0]) (Multiplicative.ofAdd 1,Multiplicative.ofAdd 0),
   raw (![0,1,1,0]) (Multiplicative.ofAdd 0,Multiplicative.ofAdd 0),
   raw (![0,1,1,0]) (Multiplicative.ofAdd 1,Multiplicative.ofAdd 0),
   raw (![1,1,1,0]) (Multiplicative.ofAdd 0,Multiplicative.ofAdd 1),
   raw (![1,1,1,0]) (Multiplicative.ofAdd 1,Multiplicative.ofAdd 1),
   raw (![0,0,0,1]) (Multiplicative.ofAdd 0,Multiplicative.ofAdd 1),
   raw (![0,0,0,1]) (Multiplicative.ofAdd 1,Multiplicative.ofAdd 1),
   raw (![1,0,0,1]) (Multiplicative.ofAdd 0,Multiplicative.ofAdd 0),
   raw (![1,0,0,1]) (Multiplicative.ofAdd 1,Multiplicative.ofAdd 0),
   raw (![0,1,0,1]) (Multiplicative.ofAdd 0,Multiplicative.ofAdd 0),
   raw (![0,1,0,1]) (Multiplicative.ofAdd 1,Multiplicative.ofAdd 0),
   raw (![1,1,0,1]) (Multiplicative.ofAdd 0,Multiplicative.ofAdd 1),
   raw (![1,1,0,1]) (Multiplicative.ofAdd 1,Multiplicative.ofAdd 1),
   raw (![0,0,1,1]) (Multiplicative.ofAdd 0,Multiplicative.ofAdd 0),
   raw (![0,0,1,1]) (Multiplicative.ofAdd 1,Multiplicative.ofAdd 0),
   raw (![1,0,1,1]) (Multiplicative.ofAdd 0,Multiplicative.ofAdd 1),
   raw (![1,0,1,1]) (Multiplicative.ofAdd 1,Multiplicative.ofAdd 1),
   raw (![0,1,1,1]) (Multiplicative.ofAdd 0,Multiplicative.ofAdd 1),
   raw (![0,1,1,1]) (Multiplicative.ofAdd 1,Multiplicative.ofAdd 1),
   raw (![1,1,1,1]) (Multiplicative.ofAdd 0,Multiplicative.ofAdd 0),
   raw (![1,1,1,1]) (Multiplicative.ofAdd 1,Multiplicative.ofAdd 0)] : Array Full)[i.val]!
def words : Fin 32 → FiniteGeneratorWord (Fin 2) := fun i =>
  (#[.one,
   (.generator 0),
   (.mul (.mul (.generator 0) (.generator 1)) (.generator 0)),
   (.mul (.generator 0) (.generator 1)),
   (.generator 1),
   (.mul (.generator 1) (.generator 0)),
   (.mul (.mul (.mul (.generator 1) (.generator 0)) (.inv (.generator 1))) (.generator 0)),
   (.mul (.mul (.generator 1) (.generator 0)) (.inv (.generator 1))),
   (.mul (.mul (.generator 0) (.inv (.generator 1))) (.generator 0)),
   (.mul (.generator 0) (.inv (.generator 1))),
   (.mul (.mul (.mul (.generator 0) (.generator 1)) (.generator 1)) (.generator 0)),
   (.mul (.mul (.generator 0) (.generator 1)) (.generator 1)),
   (.mul (.mul (.mul (.generator 1) (.generator 0)) (.generator 1)) (.generator 0)),
   (.mul (.mul (.generator 1) (.generator 0)) (.generator 1)),
   (.mul (.mul (.mul (.mul (.generator 1) (.generator 0)) (.generator 1)) (.generator 1)) (.generator 0)),
   (.mul (.mul (.mul (.generator 1) (.generator 0)) (.generator 1)) (.generator 1)),
   (.inv (.generator 1)),
   (.mul (.inv (.generator 1)) (.generator 0)),
   (.mul (.mul (.mul (.inv (.generator 1)) (.generator 0)) (.inv (.generator 1))) (.generator 0)),
   (.mul (.mul (.inv (.generator 1)) (.generator 0)) (.inv (.generator 1))),
   (.mul (.generator 1) (.generator 1)),
   (.mul (.mul (.generator 1) (.generator 1)) (.generator 0)),
   (.mul (.mul (.mul (.mul (.generator 1) (.generator 1)) (.generator 0)) (.generator 1)) (.generator 0)),
   (.mul (.mul (.mul (.generator 1) (.generator 1)) (.generator 0)) (.generator 1)),
   (.mul (.mul (.mul (.inv (.generator 1)) (.generator 0)) (.generator 1)) (.generator 0)),
   (.mul (.mul (.inv (.generator 1)) (.generator 0)) (.generator 1)),
   (.mul (.mul (.mul (.mul (.inv (.generator 1)) (.generator 0)) (.generator 1)) (.generator 1)) (.generator 0)),
   (.mul (.mul (.mul (.inv (.generator 1)) (.generator 0)) (.generator 1)) (.generator 1)),
   (.mul (.mul (.mul (.mul (.generator 1) (.generator 1)) (.generator 0)) (.inv (.generator 1))) (.generator 0)),
   (.mul (.mul (.mul (.generator 1) (.generator 1)) (.generator 0)) (.inv (.generator 1))),
   (.mul (.mul (.mul (.mul (.mul (.generator 1) (.generator 1)) (.generator 0)) (.generator 1)) (.generator 1)) (.generator 0)),
   (.mul (.mul (.mul (.mul (.generator 1) (.generator 1)) (.generator 0)) (.generator 1)) (.generator 1))] : Array (FiniteGeneratorWord (Fin 2)))[i.val]!
private theorem word_equations : ∀ i : Fin 32,
    (words i).eval fullGenerators=states i := by decide +kernel
private theorem state_cover : ∀ (v : Vector) (b : FourBlockKleinSignBase.Base),
    KleinParitySignedBinaryTop.parity (raw v b)=1 → ∃ i : Fin 32, states i=raw v b := by decide +kernel

theorem generators_full : Subgroup.closure (Set.range generators)=⊤ := by
  apply top_unique
  intro g _
  obtain ⟨i,hi⟩ := state_cover g.val.left.toAdd.val g.val.right g.property
  have he : (words i).eval generators=g := by
    apply Subtype.ext
    have hm := (words i).map_eval (Group.subtype) generators
    have hg : (fun j : Fin 2 => Group.subtype (generators j))=fullGenerators := by
      funext j
      fin_cases j <;> rfl
    rw [hg] at hm
    exact hm.trans ((word_equations i).trans hi)
  rw [← he]
  exact (words i).eval_mem_closure generators

theorem abelianization_cover_surjective : Function.Surjective
    (TwoAxisAbelianizationCover.cover X Y) := by
  apply TwoAxisAbelianizationCover.cover_surjective X Y generators generators_full
  intro i
  fin_cases i
  · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
end SymmetricSubgroupAsymptotics.Row246Signed32WordCertificate
