import SymmetricSubgroupAsymptotics.Selected1071TargetLocalGenerators

/-! Faithful synchronized A4 coordinates on the actual generated target.
The finite generator receipts propagate through its original closure. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1071QuotientGraph

private theorem targetLocals_even (g : literalTarget) (i : Fin 3) :
    targetLocals g i∈alternatingGroup (Fin 4) := by
  let P : Subgroup (Fin 3 → Equiv.Perm (Fin 4)) :=
    Subgroup.pi Set.univ (fun _ => alternatingGroup (Fin 4))
  have hle : Subgroup.closure (Set.range targetSource)≤P.comap targetLocals := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    change targetLocals (targetSource j)∈P
    rw [targetLocals_generator]
    exact fun i _ => localGenerator_even j i
  have hg : g∈Subgroup.closure (Set.range targetSource) := by
    rw [targetSource_generates]; trivial
  exact hle hg i (Set.mem_univ i)

def targetAlternating : literalTarget →* (Fin 3 → NaturalA4ScalarFourHead.G) where
  toFun g i := ⟨targetLocals g i,targetLocals_even g i⟩
  map_one' := by funext i; apply Subtype.ext; exact congrFun targetLocals.map_one i
  map_mul' g h := by funext i; apply Subtype.ext; exact congrFun (targetLocals.map_mul g h) i

theorem targetAlternating_generator (j : Fin 4) (i : Fin 3) :
    targetAlternating (targetSource j) i=alternatingGenerator j i :=
  Subtype.ext (congrFun (targetLocals_generator j) i)

theorem targetAlternating_injective : Function.Injective targetAlternating := by
  intro g h he
  apply targetLocals_injective
  funext i
  exact congrArg Subtype.val (congrFun he i)

private def localTop (i : Fin 3) : literalTarget →* CyclicThree where
  toFun g := NaturalA4ScalarFourHead.top (targetAlternating g i)
  map_one' := by rw [map_one]; exact map_one _
  map_mul' g h := by rw [map_mul]; exact map_mul _ _ _

theorem targetAlternating_common (g : literalTarget) (i : Fin 3) :
    NaturalA4ScalarFourHead.top (targetAlternating g i)=
      NaturalA4ScalarFourHead.top (targetAlternating g 0) := by
  have he : localTop i=localTop 0 :=
    MonoidHom.eq_of_eqOn_dense targetSource_generates (by
      rintro _ ⟨j,rfl⟩
      change NaturalA4ScalarFourHead.top (targetAlternating (targetSource j) i)=
        NaturalA4ScalarFourHead.top (targetAlternating (targetSource j) 0)
      rw [targetAlternating_generator,targetAlternating_generator]
      exact alternatingGenerator_common j i)
  exact DFunLike.congr_fun he g

def originalAlternating : Original →* (Fin 3 → NaturalA4ScalarFourHead.G) :=
  targetAlternating.comp originalToTarget

theorem originalAlternating_ker : originalAlternating.ker=originalKernel := by
  rw [← originalToTarget_ker]
  ext g
  change targetAlternating (originalToTarget g)=1 ↔ originalToTarget g=1
  exact map_eq_one_iff targetAlternating targetAlternating_injective

end SymmetricSubgroupAsymptotics.Selected1071QuotientGraph
