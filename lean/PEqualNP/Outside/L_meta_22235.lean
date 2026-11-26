import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22235_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness : Circuit :=
  ⟨[⟨.or, [1, 3]⟩,
     ⟨.or, [6, 4]⟩,
     ⟨.or, [7, 5]⟩,
     ⟨.not, [8]⟩,
     ⟨.and, [2, 9]⟩,
     ⟨.or, [3, 4]⟩,
     ⟨.or, [11, 5]⟩,
     ⟨.and, [0, 12]⟩,
     ⟨.or, [10, 13]⟩,
     ⟨.and, [1, 11]⟩,
     ⟨.or, [14, 15]⟩], 16⟩

private def gateOK (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => decide (g.inputs.length ≤ 2)
  | _ => false

private theorem shape : FanInTwo witness := by
  have checked : witness.gates.all gateOK = true := by decide +kernel
  intro g hg
  have good := List.all_eq_true.mp checked g hg
  cases h : g.op <;> simp [gateOK, h] at good ⊢ <;> assumption

end PEqualNP.Outside.L_meta_22235_aux

open PEqualNP.Outside.L_meta_22235_aux in
theorem PEqualNP.Outside.L_meta_22235 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17980 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, shape, by decide +kernel, by decide +kernel⟩
