import Applications.Search.OrderedMap.Interface
import Mathlib.Data.List.AList

/-!
# Association-list realizations of the shared map contract

VFA's raw list retains shadowed bindings; FDSA-XA01 uses the actual Mathlib
`AList` insertion, which erases an older binding before prepending. Both realize
the existing partial-map interface. Their observations agree, while their raw
entries need not. Chronological binding lists are reversed before they become
the raw first-match list representation.

The VFA source is the retained table-observation draft identified in
`OrderedMap.Observations`. The AList adaptation comes from FDSA-XA01 donor
`20a5b5537a704be016d09e4eb31db0dad8a12d61`, `Applications/Collections/AList.lean`.
Deletion and the original six-law Map contract remain separately preserved.
The adapted FDSA contract carries the following retained source notice.

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

namespace Search.OrderedMap
universe u v
variable {κ : Type u} {ν : Type v}

/-- The complete partial-function model has no finite-support requirement. -/
def functions (κ : Type u) (ν : Type v) [DecidableEq κ] : Ops κ ν (Meaning κ ν) where
  empty := fun _ => none
  bind := write
  lookup query m := m query

theorem functions_laws [DecidableEq κ] : Laws (functions κ ν) id where
  empty := rfl
  bind _ _ _ := rfl
  lookup _ _ := rfl

/-- First matching binding wins; repeated keys and shadowed entries are allowed. -/
def listLookup [DecidableEq κ] (query : κ) : List (κ × ν) → Option ν
  | [] => none
  | (key, value) :: rest => if query = key then some value else listLookup query rest

def listObserve [DecidableEq κ] (entries : List (κ × ν)) : Meaning κ ν :=
  fun query => listLookup query entries

def lists (κ : Type u) (ν : Type v) [DecidableEq κ] : Ops κ ν (List (κ × ν)) where
  empty := []
  bind key value entries := (key, value) :: entries
  lookup := listLookup

theorem lists_laws [DecidableEq κ] : Laws (lists κ ν) listObserve where
  empty := rfl
  bind _ _ _ := rfl
  lookup _ _ := rfl

/-- Executing chronological writes prepends them in reverse order, keeping an
arbitrary initial suffix. This relates the two distinct list interpretations. -/
theorem bindAll_lists [DecidableEq κ] (bindings entries : List (κ × ν)) :
    bindAll (lists κ ν) bindings entries = bindings.reverse ++ entries := by
  induction bindings generalizing entries with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
      change bindAll (lists κ ν) rest ((key, value) :: entries) =
        ((key, value) :: rest).reverse ++ entries
      rw [ih, List.reverse_cons, List.append_assoc]
      rfl

theorem listObserve_reverse_append [DecidableEq κ] (bindings entries : List (κ × ν)) :
    listObserve (bindings.reverse ++ entries) = writeAll bindings (listObserve entries) := by
  rw [← bindAll_lists]
  exact lists_laws.bindAll_correct bindings entries

def alistObserve [DecidableEq κ] (m : AList (fun _ : κ => ν)) : Meaning κ ν :=
  fun query => AList.lookup query m

/-- This uses standard AList insertion and lookup, not a copied search routine.
Uniqueness is intrinsic to its carrier; payloads need no default or equality. -/
def alists (κ : Type u) (ν : Type v) [DecidableEq κ] :
    Ops κ ν (AList (fun _ : κ => ν)) where
  empty := ∅
  bind := AList.insert
  lookup query m := AList.lookup query m

theorem alists_laws [DecidableEq κ] : Laws (alists κ ν) alistObserve where
  empty := by
    funext query
    exact AList.lookup_empty query
  bind key value m := by
    funext query
    change AList.lookup query (AList.insert key value m) =
      if query = key then some value else AList.lookup query m
    by_cases h : query = key
    · subst query
      rw [ite_eq_left rfl]
      exact AList.lookup_insert m
    · rw [ite_eq_right h]
      exact AList.lookup_insert_ne h
  lookup _ _ := rfl

end Search.OrderedMap
