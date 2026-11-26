import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23577_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness : Circuit where
  gates :=
    [⟨.or, [0, 4]⟩,
     ⟨.or, [1, 5]⟩,
     ⟨.or, [2, 10]⟩,
     ⟨.or, [10, 11]⟩,
     ⟨.or, [11, 7]⟩,
     ⟨.or, [14, 8]⟩,
     ⟨.or, [15, 9]⟩,
     ⟨.or, [16, 3]⟩,
     ⟨.and, [12, 17]⟩,
     ⟨.or, [18, 6]⟩,
     ⟨.and, [13, 19]⟩]
  output := 20

private def gateOK (g : Gate) : Bool :=
  match g.op with
  | .and | .or => decide (g.inputs.length ≤ 2)
  | _ => false

private theorem witness_mono : Monotone2 witness := by
  have checked : witness.gates.all gateOK = true := by decide +kernel
  intro g hg
  have good := List.all_eq_true.mp checked g hg
  cases hop : g.op <;> simp [gateOK, hop] at good ⊢ <;> assumption

end PEqualNP.Outside.L_meta_23577_aux

open PEqualNP.Outside.L_meta_23577_aux in
theorem PEqualNP.Outside.L_meta_23577 :
    (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (270718 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  refine ⟨witness, witness_mono, by decide, ?_⟩
  decide +kernel
