import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20662_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness : Circuit :=
  ⟨[⟨.or, [5, 6]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [7, 12]⟩,
    ⟨.and, [5, 11]⟩, ⟨.and, [4, 13]⟩, ⟨.or, [14, 15]⟩], 16⟩

private lemma admissible : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]

end PEqualNP.Outside.L_meta_20662_aux

open PEqualNP.Outside.L_meta_20662_aux in
theorem PEqualNP.Outside.L_meta_20662 :
    PEqualNP.Represents.RepSizeAtMost
      (fun u v : Fin 5 => (15762432 : ℕ).testBit (5 * u.val + v.val)) 7 :=
  ⟨witness, admissible, by decide, by decide +kernel⟩
