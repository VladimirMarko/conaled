import SquareKit.ValidGraphs
import Mathlib.Logic.Function.Basic

/-!
# Map operations, laws and an ordinary client

The six laws restate the Map contract in FDSA Chapter 6, Figure 6.2, and
`Map_Specs.thy` by Tobias Nipkow at Isabelle revision
`f86f290225eebcc52c1ae7dba2e098f405f51c21`. Pointwise mutation clauses avoid
requiring a key decision in the contract; the theorems using `Function.update`
state that additional notation requirement explicitly. Lookup is the model
observation itself. The model permits every partial function, without a finite
support, injectivity or surjectivity requirement on a realization.

The adapted source contract retains the following Isabelle notice.

ISABELLE COPYRIGHT NOTICE, LICENCE AND DISCLAIMER.

Copyright (c) 1986-2026,
  University of Cambridge,
  Technische Universitaet Muenchen,
  and contributors.

All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

* Redistributions of source code must retain the above copyright notice,
  this list of conditions and the following disclaimer.
* Redistributions in binary form must reproduce the above copyright notice,
  this list of conditions and the following disclaimer in the documentation
  and/or other materials provided with the distribution.
* Neither the name of the University of Cambridge or the Technische
  Universitaet Muenchen nor the names of their contributors may be used to
  endorse or promote products derived from this software without specific
  prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
POSSIBILITY OF SUCH DAMAGE.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Collections.Maps

universe u v w w'

/-- The operations contain neither invariant evidence nor a separate decoder. -/
structure Ops (α : Type u) (β : Type v) (M : Type w) where
  empty : M
  update : α → β → M → M
  delete : α → M → M
  lookup : M → α → Option β

variable {α : Type u} {β : Type v} {M : Type w} {N : Type w'}

/-- The six Map laws, with each mutation's semantics grouped as one field. -/
structure Laws (ops : Ops α β M) (Valid : M → Prop) : Prop where
  empty_lookup : ops.lookup ops.empty = fun _ => none
  empty_valid : Valid ops.empty
  update_lookup : ∀ a x m, Valid m →
    ops.lookup (ops.update a x m) a = some x ∧
      ∀ k, k ≠ a → ops.lookup (ops.update a x m) k = ops.lookup m k
  update_valid : ∀ a x m, Valid m → Valid (ops.update a x m)
  delete_lookup : ∀ a m, Valid m →
    ops.lookup (ops.delete a m) a = none ∧
      ∀ k, k ≠ a → ops.lookup (ops.delete a m) k = ops.lookup m k
  delete_valid : ∀ a m, Valid m → Valid (ops.delete a m)

/-- Update the first key, update the second, then delete the first. This
executable client receives only operations and ordinary arguments. -/
def client (ops : Ops α β M) (a : α) (x : β) (b : α) (y : β) (m : M) : M :=
  ops.delete a (ops.update b y (ops.update a x m))

open SquareKit.ValidGraphs

/-- Lookup is already the abstraction function. Its observation schema needs
no additional law and gives an ordinary Option result with trivial validity. -/
theorem lookup_preserves (ops : Ops α β M) (Valid : M → Prop) (a : α) :
    Relator.LiftFun (validGraph Valid ops.lookup)
      (validGraph (fun _ : Option β => True) id)
      (fun m => ops.lookup m a) (fun f => f a) := by
  apply (liftFun_iff Valid ops.lookup (fun _ : Option β => True) id
    (fun m => ops.lookup m a) (fun f => f a)).2
  intro m _
  exact ⟨True.intro, rfl⟩

namespace Laws

variable {ops : Ops α β M} {Valid : M → Prop}

/-- The grouped update law is exactly the source's function-update equation. -/
theorem lookup_update_eq (h : Laws ops Valid) [DecidableEq α]
    (a : α) (x : β) {m : M} (hm : Valid m) :
    ops.lookup (ops.update a x m) = Function.update (ops.lookup m) a (some x) :=
  Function.eq_update_iff.2 (h.update_lookup a x m hm)

/-- The grouped delete law is exactly the source's function-update equation. -/
theorem lookup_delete_eq (h : Laws ops Valid) [DecidableEq α]
    (a : α) {m : M} (hm : Valid m) :
    ops.lookup (ops.delete a m) = Function.update (ops.lookup m) a none :=
  Function.eq_update_iff.2 (h.delete_lookup a m hm)

/-- Initialization supplies both unconditional empty obligations. -/
theorem empty_related (h : Laws ops Valid) :
    validGraph Valid ops.lookup ops.empty (fun _ => none) :=
  ⟨h.empty_valid, h.empty_lookup⟩

/-- Mutation preservation uses the shared invariant/observation bridge. -/
theorem update_preserves (h : Laws ops Valid) [DecidableEq α] (a : α) (x : β) :
    Relator.LiftFun (validGraph Valid ops.lookup) (validGraph Valid ops.lookup)
      (ops.update a x) (fun f => Function.update f a (some x)) := by
  apply (liftFun_iff Valid ops.lookup Valid ops.lookup
    (ops.update a x) (fun f => Function.update f a (some x))).2
  intro m hm
  exact ⟨h.update_valid a x m hm, h.lookup_update_eq a x hm⟩

/-- Deletion retains output validity as well as its whole lookup equation. -/
theorem delete_preserves (h : Laws ops Valid) [DecidableEq α] (a : α) :
    Relator.LiftFun (validGraph Valid ops.lookup) (validGraph Valid ops.lookup)
      (ops.delete a) (fun f => Function.update f a none) := by
  apply (liftFun_iff Valid ops.lookup Valid ops.lookup
    (ops.delete a) (fun f => Function.update f a none)).2
  intro m hm
  exact ⟨h.delete_valid a m hm, h.lookup_delete_eq a hm⟩

/-- Each certificate refers to the actual preceding result of the client. -/
theorem client_intermediate_valid (h : Laws ops Valid)
    (a : α) (x : β) (b : α) (y : β) {m : M} (hm : Valid m) :
    Valid (ops.update a x m) ∧
      Valid (ops.update b y (ops.update a x m)) ∧
        Valid (client ops a x b y m) := by
  have hfirst := h.update_valid a x m hm
  have hsecond := h.update_valid b y (ops.update a x m) hfirst
  exact ⟨hfirst, hsecond, h.delete_valid a _ hsecond⟩

theorem client_valid (h : Laws ops Valid)
    (a : α) (x : β) (b : α) (y : β) {m : M} (hm : Valid m) :
    Valid (client ops a x b y m) :=
  (h.client_intermediate_valid a x b y hm).2.2

/-- The full client observation follows by applying the three source equations
to its actual valid intermediate states. -/
theorem client_lookup_eq (h : Laws ops Valid) [DecidableEq α]
    (a : α) (x : β) (b : α) (y : β) {m : M} (hm : Valid m) :
    ops.lookup (client ops a x b y m) =
      Function.update
        (Function.update (Function.update (ops.lookup m) a (some x)) b (some y))
        a none := by
  have hstates := h.client_intermediate_valid a x b y hm
  change ops.lookup (ops.delete a (ops.update b y (ops.update a x m))) = _
  rw [h.lookup_delete_eq a hstates.2.1,
    h.lookup_update_eq b y hstates.1, h.lookup_update_eq a x hm]

theorem client_lookup_deleted (h : Laws ops Valid)
    (a : α) (x : β) (b : α) (y : β) {m : M} (hm : Valid m) :
    ops.lookup (client ops a x b y m) a = none :=
  (h.delete_lookup a _ (h.client_intermediate_valid a x b y hm).2.1).1

theorem client_lookup_inserted (h : Laws ops Valid)
    (a : α) (x : β) (b : α) (y : β) {m : M} (hm : Valid m) (hba : b ≠ a) :
    ops.lookup (client ops a x b y m) b = some y := by
  have hstates := h.client_intermediate_valid a x b y hm
  calc
    ops.lookup (client ops a x b y m) b =
        ops.lookup (ops.update b y (ops.update a x m)) b :=
      (h.delete_lookup a _ hstates.2.1).2 b hba
    _ = some y := (h.update_lookup b y _ hstates.1).1

/-- Coinciding keys are permitted; the final deletion determines their query. -/
theorem client_lookup_same (h : Laws ops Valid)
    (a : α) (x y : β) {m : M} (hm : Valid m) :
    ops.lookup (client ops a x a y m) a = none :=
  h.client_lookup_deleted a x a y hm

theorem client_lookup_untouched (h : Laws ops Valid)
    (a : α) (x : β) (b : α) (y : β) {m : M} (hm : Valid m)
    (k : α) (hka : k ≠ a) (hkb : k ≠ b) :
    ops.lookup (client ops a x b y m) k = ops.lookup m k := by
  have hstates := h.client_intermediate_valid a x b y hm
  calc
    ops.lookup (client ops a x b y m) k =
        ops.lookup (ops.update b y (ops.update a x m)) k :=
      (h.delete_lookup a _ hstates.2.1).2 k hka
    _ = ops.lookup (ops.update a x m) k :=
      (h.update_lookup b y _ hstates.1).2 k hkb
    _ = ops.lookup m k := (h.update_lookup a x m hm).2 k hka

/-- This specified operation-only client preserves agreement of observations
across lawful representations, without requiring equal concrete states. -/
theorem client_observation_agrees (h : Laws ops Valid)
    {other : Ops α β N} {OtherValid : N → Prop} (hother : Laws other OtherValid)
    (a : α) (x : β) (b : α) (y : β) {m : M} {n : N}
    (hm : Valid m) (hn : OtherValid n) (hobs : ops.lookup m = other.lookup n) :
    ops.lookup (client ops a x b y m) = other.lookup (client other a x b y n) := by
  classical
  rw [h.client_lookup_eq a x b y hm, hother.client_lookup_eq a x b y hn, hobs]

end Laws
end Collections.Maps
