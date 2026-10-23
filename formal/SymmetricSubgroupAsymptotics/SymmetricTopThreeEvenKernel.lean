import SymmetricSubgroupAsymptotics.ThreePointPermutationClassBound

/-! The genuine even-top intermediate subgroup for an original S3
quotient. An outside transposition has no nontrivial commuting image
in the even quotient, so its intermediate centralizer lies in the
ORIGINAL full top kernel. No complement is chosen. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SymmetricTopThreeEvenKernel
open PrimeIndexAbelianCentralizers ThreePointPermutationClassBound
variable {G : Type} [Group G] (f:G→*Equiv.Perm (Fin 3))

abbrev EvenTop : Subgroup G := (alternatingGroup (Fin 3)).comap f

def evenTopMap : EvenTop f→*alternatingGroup (Fin 3) where
  toFun x := ⟨f x.val,x.property⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' x y := Subtype.ext (map_mul f x.val y.val)

theorem evenTopMap_surjective (hf:Function.Surjective f) :
    Function.Surjective (evenTopMap f) := by
  intro a
  obtain ⟨g,hg⟩ := hf a.val
  refine ⟨⟨g,?_⟩,Subtype.ext hg⟩
  change f g∈alternatingGroup (Fin 3)
  rw [hg]
  exact a.property

theorem evenTop_index (hf:Function.Surjective f) : (EvenTop f).index=2 :=
  ((alternatingGroup (Fin 3)).index_comap_of_surjective hf).trans
    (alternatingGroup.index_eq_two (α:=Fin 3))

theorem kernel_le_evenTop : f.ker≤EvenTop f := by
  intro g hg
  change f g∈alternatingGroup (Fin 3)
  rw [MonoidHom.mem_ker.mp hg]
  exact Subgroup.one_mem _

theorem outside_commuting_even_mem_kernel (x:G) (hx:x∉EvenTop f)
    (y:EvenTop f) (hxy:Commute x (y:G)) : (y:G)∈f.ker := by
  let N := alternatingGroup (Fin 3)
  letI : IsCyclic N := alternatingGroup.isCyclic_of_card_le_three (by norm_num)
  have hx' : f x∉N := hx
  let n:N := ⟨f y.val,y.property⟩
  have hn : n∈fixedKernel N (f x) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hxy.map f).eq.symm
  rw [fixedKernel_eq_centralKernel N 2 Nat.prime_two
      (alternatingGroup.index_eq_two (α:=Fin 3)) (f x) hx',centralKernel_eq_bot N] at hn
  have he : n=1 := Subgroup.mem_bot.mp hn
  exact MonoidHom.mem_ker.mpr (congrArg (fun z:N=>z.val) he)

end SymmetricSubgroupAsymptotics.SymmetricTopThreeEvenKernel
