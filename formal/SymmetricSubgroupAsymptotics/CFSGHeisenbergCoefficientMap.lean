import SymmetricSubgroupAsymptotics.CFSGHeisenbergCoordinateGroup

/-! Entrywise coefficient maps preserve the actual ordered Heisenberg
cocycle. In particular the prime-field subgroup injects into the same
coordinate group over any field of the given characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHeisenbergCoefficientMap
open CFSGHeisenbergCoordinateGroup
variable {F K:Type*}[CommRing F][CommRing K]{m:ℕ}

def map (f:F→+*K) : Element F m→*Element K m where
  toFun g := ⟨f∘g.a,f∘g.b,f g.c⟩
  map_one' := by
    apply Element.ext
    · funext i
      change f 0=0
      exact map_zero f
    · funext i
      change f 0=0
      exact map_zero f
    · change f 0=0
      exact map_zero f
  map_mul' g h := by
    apply Element.ext
    · ext i;exact map_add f _ _
    · ext i;exact map_add f _ _
    · change f (g.c+h.c+dot g.b h.a)=f g.c+f h.c+dot (f∘g.b) (f∘h.a)
      simp only [map_add,dot,map_sum,map_mul,Function.comp_apply]

theorem map_injective (f:F→+*K)(hf:Function.Injective f) : Function.Injective (map (m:=m) f) := by
  intro g h he
  apply Element.ext
  · funext i
    exact hf (congrFun (congrArg Element.a he) i)
  · funext i
    exact hf (congrFun (congrArg Element.b he) i)
  · exact hf (congrArg Element.c he)

theorem map_central (f:F→+*K)(c:Multiplicative F) :
    map (m:=m) f (central c)=central (Multiplicative.ofAdd (f c.toAdd)) := by
  apply Element.ext
  · funext i
    change f 0=0
    exact map_zero f
  · funext i
    change f 0=0
    exact map_zero f
  · rfl

end SymmetricSubgroupAsymptotics.CFSGHeisenbergCoefficientMap
