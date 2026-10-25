import SymmetricSubgroupAsymptotics.CFSGCentralKernelPSubgroups

/-! A disjoint ordered pair of quotient Sylows lifts to a disjoint ordered
pair of source Sylows. Only the Sylows are lifted, never an automorphism.
The central kernel is retained and actual injectivity on one source Sylow
separates all p-subgroups by the previously proved p-element theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CentralKernelSylowPairLift
variable {G H : Type*} [Group G] [Group H]

theorem inf_eq_bot_of_map_inf_eq_bot (f : G →* H) (U V : Subgroup G)
    (hi : Function.Injective (f.comp U.subtype))
    (h : U.map f ⊓ V.map f = ⊥) : U ⊓ V = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hm : f x ∈ U.map f ⊓ V.map f :=
    ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
  have hf : f x = 1 := Subgroup.mem_bot.mp (h ▸ hm)
  have he : f.comp U.subtype ⟨x, hx.1⟩ = f.comp U.subtype 1 := by
    change f x = f 1
    exact hf.trans (map_one f).symm
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val (hi he))

theorem exists_lift_pair [Finite G] {p : ℕ} [Fact p.Prime]
    (f : G →* H) (hf : Function.Surjective f) (P : Sylow p G)
    (hP : Function.Injective (f.comp (P : Subgroup G).subtype))
    (hker : f.ker ≤ Subgroup.center G)
    (A B : Sylow p H) (hAB : (A : Subgroup H) ⊓ (B : Subgroup H) = ⊥) :
    ∃ R S : Sylow p G,
      (R : Subgroup G).map f = (A : Subgroup H) ∧
      (S : Subgroup G).map f = (B : Subgroup H) ∧
      (R : Subgroup G) ⊓ (S : Subgroup G) = ⊥ := by
  obtain ⟨R, hR⟩ := Sylow.mapSurjective_surjective hf p A
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective hf p B
  have hRm : (R : Subgroup G).map f = (A : Subgroup H) :=
    congrArg (fun T : Sylow p H => (T : Subgroup H)) hR
  have hSm : (S : Subgroup G).map f = (B : Subgroup H) :=
    congrArg (fun T : Sylow p H => (T : Subgroup H)) hS
  refine ⟨R, S, hRm, hSm, ?_⟩
  apply inf_eq_bot_of_map_inf_eq_bot f (R : Subgroup G) (S : Subgroup G)
    (CFSGCentralKernelPElements.p_subgroup_injective f P hP hker
      (R : Subgroup G) R.isPGroup')
  rw [hRm, hSm]
  exact hAB

end SymmetricSubgroupAsymptotics.CentralKernelSylowPairLift
