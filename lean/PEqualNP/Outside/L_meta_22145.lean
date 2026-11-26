import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22145_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness : Circuit :=
  ⟨[⟨.or, [1, 3]⟩,
     ⟨.not, [6]⟩,
     ⟨.and, [0, 7]⟩,
     ⟨.or, [0, 2]⟩,
     ⟨.or, [9, 3]⟩,
     ⟨.or, [10, 5]⟩,
     ⟨.not, [11]⟩,
     ⟨.and, [1, 12]⟩,
     ⟨.and, [2, 3]⟩,
     ⟨.or, [8, 13]⟩,
     ⟨.or, [15, 14]⟩], 16⟩

private def gateOK (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => decide (g.inputs.length ≤ 2)
  | _ => false

private theorem shape : FanInTwo witness := by
  have checked : witness.gates.all gateOK = true := by decide +kernel
  intro g hg
  have good := List.all_eq_true.mp checked g hg
  cases h : g.op <;> simp [gateOK, h] at good ⊢ <;> assumption

end PEqualNP.Outside.L_meta_22145_aux

open PEqualNP.Outside.L_meta_22145_aux in
theorem PEqualNP.Outside.L_meta_22145 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33973 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, shape, by decide +kernel, by decide +kernel⟩
