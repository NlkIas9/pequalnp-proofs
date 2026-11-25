import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_5813_1 :
  (∀ (C : Circuit) (line : Fin 13),
    Monotone2 C → ReadsBack 27 C → 2 ≤ andPairs 27 C →
    let D : Finset (Fin 13) := {0, 1, 3, 9}
    let X := fun (P L : Finset (Fin 13)) =>
      (List.ofFn (fun p => decide (p ∈ P)) ++ List.ofFn (fun l => decide (l ∈ L))) ++ [false]
    (0 - line ∈ D) →
    (∀ p l : Fin 13, p - l ∈ D → p ≠ 0 ∨ l ≠ line → C.eval (X {p} {l}) = true) →
    (∀ Q : Finset (Fin 13), Q.card = 4 → (∀ k : Fin 13, (Q.filter (fun p => p - k ∈ D)).card ≤ 2) →
      C.eval (X Q (Finset.univ.filter (fun l => ∀ p ∈ Q, p - l ∉ D))) = false) →
    (∀ p a l b : Fin 13, p - l ∉ D → p - b ∉ D → a - l ∉ D → a - b ∉ D →
      C.eval (X {p,a} {l,b}) = false) → 63 ≤ C.size) →
  (∀ (C : Circuit) (line : Fin 13),
    Monotone2 C → ReadsBack 27 C → 2 ≤ andPairs 27 C →
    let D : Finset (Fin 13) := {0, 1, 3, 9}
    let X := fun (P L : Finset (Fin 13)) =>
      (List.ofFn (fun p => decide (p ∈ P)) ++ List.ofFn (fun l => decide (l ∈ L))) ++ [true]
    (0 - line ∈ D) →
    (∀ p l : Fin 13, p - l ∈ D → p ≠ 0 ∨ l ≠ line → C.eval (X {p} {l}) = true) →
    (∀ Q : Finset (Fin 13), Q.card = 4 → (∀ k : Fin 13, (Q.filter (fun p => p - k ∈ D)).card ≤ 2) →
      C.eval (X Q (Finset.univ.filter (fun l => ∀ p ∈ Q, p - l ∉ D))) = false) →
    (∀ p a l b : Fin 13, p - l ∉ D → p - b ∉ D → a - l ∉ D → a - b ∉ D →
      C.eval (X {p,a} {l,b}) = false) → 63 ≤ C.size) →
  (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (13 : ℕ)) (x4 : Bool),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x1 →       (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (27 : ℕ) x1 →         have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x9 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x9 x10 : Finset (Fin (13 : ℕ))) => ((List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ [x4];         (∀ (x10 x11 : Fin (13 : ℕ)), x10 - x11 ∈ x8 → x10 ≠ x2 ∨ x11 ≠ x3 → x1.eval (x9 {x10} {x11}) = Bool.true) → (∀ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) → (∀ (x13 : Fin (13 : ℕ)), {x14 ∈ x11 | x14 - x13 ∈ x8}.card ≤ (2 : ℕ)) → x1.eval (x9 x11 {x14 : Fin (13 : ℕ) | ∀ x15 ∈ x11, x15 - x14 ∉ x8}) = Bool.false) → (∀ (x12 x13 x14 x15 : Fin (13 : ℕ)), x12 - x14 ∉ x8 → x12 - x15 ∉ x8 → x13 - x14 ∉ x8 → x13 - x15 ∉ x8 → x1.eval (x9 {x12, x13} {x14, x15}) = Bool.false) → (63 : ℕ) ≤ x1.size) := by
  intro noBit yesBit C p0 l0 bit mono back pairBound D X pos quad rect
  let shift (p : Fin 13) := p + p0
  let unshift (p : Fin 13) := p - p0
  have shiftedBack (p : Fin 13) : unshift (shift p) = p := by simp [shift, unshift]
  have unshiftedBack (p : Fin 13) : shift (unshift p) = p := by simp [shift, unshift]
  have shiftInj : Function.Injective shift := fun a b h => by
    have e := congrArg unshift h
    simpa only [shiftedBack] using e
  have edgeShift (p l : Fin 13) : shift p - shift l = p - l := by
    simp [shift]
  let moved (P : Finset (Fin 13)) := P.image shift
  have memMoved (P : Finset (Fin 13)) (p : Fin 13) : shift p ∈ moved P ↔ p ∈ P :=
    by
      rw [Finset.mem_image]
      constructor
      · rintro ⟨q, hq, e⟩
        exact shiftInj e ▸ hq
      · intro mem
        exact ⟨p, mem, rfl⟩
  let wire (k : ℕ) : ℕ :=
    if k < 13 then (unshift (Fin.ofNat 13 k)).val
    else if k < 26 then 13 + (unshift (Fin.ofNat 13 (k - 13))).val else k
  have wireBelow (k : ℕ) (hk : k < 26) : wire k < 26 := by
    dsimp only [wire]
    split
    · exact (unshift (Fin.ofNat 13 k)).isLt.trans (by decide)
    · have h := (unshift (Fin.ofNat 13 (k - 13))).isLt
      omega
  have wireFixed (k : ℕ) (hk : 26 ≤ k) : wire k = k := by
    simp [wire, show ¬ k < 13 by omega, show ¬ k < 26 by omega]
  have boundWire (k n : ℕ) (hn : 26 ≤ n) (hk : k < n) : wire k < n := by
    by_cases h : k < 26
    · exact (wireBelow k h).trans_le hn
    · simpa only [wireFixed k (by omega)] using hk
  let remap (g : Gate) : Gate := ⟨g.op, g.inputs.map wire⟩
  let C' : Circuit := ⟨C.gates.map remap, wire C.output⟩
  have sameLength : C'.gates.length = C.gates.length := List.length_map remap
  have sameSize : C'.size = C.size := sameLength
  have sameOp (k : ℕ) : (gateAt C' k).op = (gateAt C k).op := by
    change ((C.gates.map remap).getD k (remap ⟨GateOp.or, []⟩)).op = (gateAt C k).op
    rw [List.getD_map]
    rfl
  have mono' : Monotone2 C' := by
    intro g hg
    obtain ⟨old, mem, rfl⟩ := List.mem_map.mp hg
    exact ⟨(mono old mem).1, by simpa [remap] using (mono old mem).2⟩
  have back' : ReadsBack 27 C' := by
    intro k hk i hi
    have oldRange : k < C.gates.length := sameLength ▸ hk
    change i ∈ ((C.gates.map remap).getD k (remap ⟨GateOp.or, []⟩)).inputs at hi
    rw [List.getD_map] at hi
    change i ∈ ((gateAt C k).inputs.map wire) at hi
    obtain ⟨old, mem, rfl⟩ := List.mem_map.mp hi
    exact boundWire old (27 + k) (by omega) (back k oldRange old mem)
  have stepCones (cs : List (List ℕ)) (g : Gate) :
      coneStep 27 cs (remap g) = coneStep 27 cs g := by
    have filtered (xs : List ℕ) :
        (xs.map wire).filter (fun w => decide (27 ≤ w ∧ w < 27 + cs.length)) =
          xs.filter (fun w => decide (27 ≤ w ∧ w < 27 + cs.length)) := by
      induction xs with
      | nil => rfl
      | cons x xs ih =>
        simp only [List.map_cons, List.filter_cons, ih]
        by_cases ht : x < 26
        · have ht' := wireBelow x ht
          simp [show ¬ 27 ≤ x by omega, show ¬ 27 ≤ wire x by omega]
        · simp [wireFixed x (by omega)]
    change cs ++ [((g.inputs.map wire).filter _).flatMap _] =
      cs ++ [(g.inputs.filter _).flatMap _]
    rw [filtered]
  have foldCones (gs : List Gate) (cs : List (List ℕ)) :
      (gs.map remap).foldl (coneStep 27) cs = gs.foldl (coneStep 27) cs := by
    induction gs generalizing cs with
    | nil => rfl
    | cons g gs ih => simp only [List.map_cons, List.foldl_cons, stepCones, ih]
  have conesEqual : cones 27 C' = cones 27 C := foldCones C.gates []
  have inConeEq (i j : ℕ) : InCone 27 C' i j ↔ InCone 27 C i j := by
    change i ∈ (cones 27 C').getD j [] ↔ i ∈ (cones 27 C).getD j []
    rw [conesEqual]
  have pairEq : andPairs 27 C' = andPairs 27 C := by
    delta andPairs
    apply congrArg Finset.card
    apply Finset.ext
    intro p
    simp only [Finset.mem_filter]
    simp only [sameLength, sameOp, inConeEq]
  have pairs' : 2 ≤ andPairs 27 C' := pairEq ▸ pairBound
  have run (gs : List Gate) (old new : List Bool)
      (lengthEq : old.length = new.length) (large : 26 ≤ old.length)
      (values : ∀ k, old.getD k false = new.getD (wire k) false) :
      ∀ k, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) old).getD k false =
        ((gs.map remap).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) new).getD (wire k) false := by
    induction gs generalizing old new with
    | nil => exact values
    | cons g gs ih =>
      let b := g.op.eval (g.inputs.map fun i => old.getD i false)
      have same : (remap g).op.eval ((remap g).inputs.map fun i => new.getD i false) = b := by
        change g.op.eval ((g.inputs.map wire).map fun i => new.getD i false) = b
        simp only [List.map_map, Function.comp_def, ← values, b]
      simp only [List.map_cons, List.foldl_cons, same]
      apply ih (old ++ [b]) (new ++ [b])
      · simp [lengthEq]
      · simp; omega
      · intro k
        by_cases h : k < old.length
        · rw [List.getD_append _ _ _ _ h,
            List.getD_append _ _ _ _ (lengthEq ▸ boundWire k old.length large h)]
          exact values k
        · have fixed : wire k = k := wireFixed k (by omega)
          rw [fixed, List.getD_append_right _ _ _ _ (by omega),
            List.getD_append_right _ _ _ _ (by omega), lengthEq]
  have leftValue (P L : Finset (Fin 13)) (p : Fin 13) :
      (X P L).getD p.val false = decide (p ∈ P) := by
    change (((List.ofFn fun q : Fin 13 => decide (q ∈ P)) ++
      List.ofFn (fun q : Fin 13 => decide (q ∈ L))) ++ [bit]).getD p.val false = _
    rw [List.getD_append _ _ _ _ (by simp; omega),
      List.getD_append _ _ _ _ (by simp)]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have rightValue (P L : Finset (Fin 13)) (l : Fin 13) :
      (X P L).getD (13 + l.val) false = decide (l ∈ L) := by
    change (((List.ofFn fun q : Fin 13 => decide (q ∈ P)) ++
      List.ofFn (fun q : Fin 13 => decide (q ∈ L))) ++ [bit]).getD (13 + l.val) false = _
    rw [List.getD_append _ _ _ _ (by simp; omega),
      List.getD_append_right _ _ _ _ (by simp)]
    simp only [List.length_ofFn, Nat.add_sub_cancel_left]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have tailValue (P L : Finset (Fin 13)) (k : ℕ) (hk : 26 ≤ k) :
      (X P L).getD k false = [bit].getD (k-26) false := by
    change (((List.ofFn fun q : Fin 13 => decide (q ∈ P)) ++
      List.ofFn (fun q : Fin 13 => decide (q ∈ L))) ++ [bit]).getD k false = _
    rw [List.getD_append_right _ _ _ _ (by simpa using hk)]
    rfl
  have leftWire (p : Fin 13) : wire p.val = (unshift p).val := by
    simp [wire]
  have rightWire (l : Fin 13) : wire (13 + l.val) = 13 + (unshift l).val := by
    have limit : 13 + l.val < 26 := by have bound := l.isLt; omega
    simp [wire, limit]
  have membership (P : Finset (Fin 13)) (p : Fin 13) : p ∈ moved P ↔ unshift p ∈ P := by
    simpa only [unshiftedBack] using memMoved P (unshift p)
  have inputEq (P L : Finset (Fin 13)) (k : ℕ) :
      (X (moved P) (moved L)).getD k false = (X P L).getD (wire k) false := by
    by_cases hl : k < 13
    · let p : Fin 13 := ⟨k,hl⟩
      change (X (moved P) (moved L)).getD p.val false = _
      change _ = (X P L).getD (wire p.val) false
      rw [leftValue, leftWire, leftValue]
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using membership P p
    · by_cases hr : k < 26
      · let l : Fin 13 := ⟨k - 13, by omega⟩
        have h : k = 13 + l.val := by dsimp [l]; omega
        rw [h, rightValue, rightWire, rightValue]
        apply Bool.eq_iff_iff.mpr
        simpa only [decide_eq_true_eq] using membership L l
      · have hk : 26 ≤ k := by omega
        rw [wireFixed k hk, tailValue _ _ k hk, tailValue _ _ k hk]
  have inputLen (P L : Finset (Fin 13)) : (X P L).length = 27 := by simp [X]
  have evalShift (P L : Finset (Fin 13)) : C.eval (X (moved P) (moved L)) = C'.eval (X P L) :=
    run C.gates _ _ (by simp [inputLen]) (by simp [inputLen]) (inputEq P L) C.output
  let line : Fin 13 := if p0 - l0 ∈ D then unshift l0 else 0
  have zeroShift : shift 0 = p0 := by simp [shift]
  have lineInc : 0 - line ∈ D := by
    by_cases h : p0 - l0 ∈ D
    · have e := edgeShift 0 (unshift l0)
      rw [zeroShift, unshiftedBack] at e
      simp [line, h, ← e]
    · simp [line, h, D]
  have newPos (p l : Fin 13) (inc : p - l ∈ D) (other : p ≠ 0 ∨ l ≠ line) :
      C'.eval (X {p} {l}) = true := by
    rw [← evalShift]
    have inc' : shift p - shift l ∈ D := edgeShift p l ▸ inc
    have other' : shift p ≠ p0 ∨ shift l ≠ l0 := by
      by_contra h
      push Not at h
      have real : p0 - l0 ∈ D := by simpa [h.1, h.2] using inc'
      have first : p = 0 := shiftInj (h.1.trans zeroShift.symm)
      have second : l = line := by
        apply shiftInj
        rw [show line = unshift l0 by simp [line,real], unshiftedBack]
        exact h.2
      exact other.elim (fun hn => hn first) (fun hn => hn second)
    simpa [moved] using pos (shift p) (shift l) inc' other'
  have surj : Function.Surjective shift := fun t => ⟨unshift t, unshiftedBack t⟩
  have filterShift (Q : Finset (Fin 13)) (k : Fin 13) :
      (moved Q).filter (fun p => p - shift k ∈ D) = moved (Q.filter fun p => p - k ∈ D) := by
    ext t
    obtain ⟨p,rfl⟩ := surj t
    simp only [Finset.mem_filter, memMoved, edgeShift]
  have missedShift (Q : Finset (Fin 13)) :
      Finset.univ.filter (fun l => ∀ p ∈ moved Q, p - l ∉ D) =
        moved (Finset.univ.filter fun l => ∀ p ∈ Q, p - l ∉ D) := by
    ext t
    obtain ⟨l,rfl⟩ := surj t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, memMoved]
    constructor
    · intro h p hp
      simpa only [edgeShift] using h (shift p) ((memMoved Q p).mpr hp)
    · intro h x hx
      obtain ⟨p,rfl⟩ := surj x
      rw [edgeShift]
      exact h p ((memMoved Q p).mp hx)
  have newQuad (Q : Finset (Fin 13)) (size : Q.card = 4)
      (sparse : ∀ k : Fin 13, (Q.filter fun p => p-k ∈ D).card ≤ 2) :
      C'.eval (X Q (Finset.univ.filter fun l => ∀ p ∈ Q, p-l ∉ D)) = false := by
    rw [← evalShift, ← missedShift]
    apply quad (moved Q)
    · simpa [moved, Finset.card_image_of_injective _ shiftInj] using size
    · intro t
      obtain ⟨k,rfl⟩ := surj t
      rw [filterShift]
      simpa [moved, Finset.card_image_of_injective _ shiftInj] using sparse k
  have newRect (p a l b : Fin 13) (h0 : p-l ∉ D) (h1 : p-b ∉ D)
      (h2 : a-l ∉ D) (h3 : a-b ∉ D) : C'.eval (X {p,a} {l,b}) = false := by
    rw [← evalShift]
    simpa [moved] using rect (shift p) (shift a) (shift l) (shift b)
      (by simpa only [edgeShift] using h0) (by simpa only [edgeShift] using h1)
      (by simpa only [edgeShift] using h2) (by simpa only [edgeShift] using h3)
  rw [← sameSize]
  cases bit
  · exact noBit C' line mono' back' pairs' lineInc newPos newQuad newRect
  · exact yesBit C' line mono' back' pairs' lineInc newPos newQuad newRect
