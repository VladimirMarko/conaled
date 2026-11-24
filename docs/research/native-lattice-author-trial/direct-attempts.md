# Direct attempt archive

Frozen #692 trial evidence. Original relative paths and SHA-256 hashes follow. Failed source versions and outputs are retained verbatim; they are not integrated declarations. Generated olean binaries are omitted.

## Direct.lean

SHA-256: `cfb3f939980dd34ec20a067e3c3ffb67fc1710712466a04098c54ff5f4ef794c`

````text
import Mathlib.Order.Hom.Lattice
import Mathlib.Tactic

namespace DirectTrial692

/-- Integer translation by three, with the specified inverse. -/
def translation : Int ≃o Int where
  toFun z := z + 3
  invFun z := z - 3
  left_inv z := by change (z + 3) - 3 = z; omega
  right_inv z := by change (z - 3) + 3 = z; omega
  map_rel_iff' := by intro a b; change (a + 3 ≤ b + 3) ↔ a ≤ b; omega

@[simp] theorem translation_apply (z : Int) : translation z = z + 3 := rfl
@[simp] theorem translation_symm_apply (z : Int) : translation.symm z = z - 3 := rfl

/-- An ordered pair together with its order witness. -/
def OrderedPair := { p : Int × Int // p.1 ≤ p.2 }

/-- Transport the full dependent value through an ordinary order isomorphism. -/
def transport (e : Int ≃o Int) (p : OrderedPair) : OrderedPair :=
  ⟨(e p.val.1, e p.val.2), e.monotone p.property⟩

theorem transport_symm_transport (e : Int ≃o Int) (p : OrderedPair) :
    transport e.symm (transport e p) = p := by
  apply Subtype.ext
  apply Prod.ext <;> simp [transport]

theorem transport_transport_symm (e : Int ≃o Int) (p : OrderedPair) :
    transport e (transport e.symm p) = p := by
  apply Subtype.ext
  apply Prod.ext <;> simp [transport]

/-- The complete translated subtype value for arbitrary ordered endpoints. -/
theorem transport_translation (x y : Int) (h : x ≤ y) :
    transport translation ⟨(x, y), h⟩ =
      (⟨(x + 3, y + 3), by omega⟩ : OrderedPair) := by
  apply Subtype.ext
  rfl

/-- Recovery includes the order witness, through equality of subtype values. -/
theorem translation_recovers (x y : Int) (h : x ≤ y) :
    transport translation.symm (transport translation ⟨(x, y), h⟩) =
      (⟨(x, y), h⟩ : OrderedPair) :=
  transport_symm_transport translation _

def gap (p : OrderedPair) : Int := p.val.2 - p.val.1

theorem gap_translation (p : OrderedPair) :
    gap (transport translation p) = gap p := by
  change (p.val.2 + 3) - (p.val.1 + 3) = p.val.2 - p.val.1
  omega

theorem translation_preserves_strictness (p : OrderedPair)
    (h : p.val.1 < p.val.2) :
    (transport translation p).val.1 < (transport translation p).val.2 :=
  translation.strictMono h

def selected : OrderedPair := ⟨(-2, 4), by norm_num⟩

theorem selected_translation :
    transport translation selected = (⟨(1, 7), by norm_num⟩ : OrderedPair) := by
  apply Subtype.ext
  norm_num [transport, selected]

theorem selected_strict :
    (transport translation selected).val.1 <
      (transport translation selected).val.2 :=
  translation_preserves_strictness selected (by norm_num [selected])

theorem selected_gap : gap (transport translation selected) = 6 := by
  rw [gap_translation]
  norm_num [gap, selected]

theorem selected_recovers :
    transport translation.symm (transport translation selected) = selected :=
  transport_symm_transport translation selected

theorem translation_nonidentity : translation 0 = 3 ∧ translation 0 ≠ 0 := by
  norm_num

theorem translation_inf (x y : Int) :
    translation (x ⊓ y) = translation x ⊓ translation y :=
  map_inf translation x y

theorem translation_sup (x y : Int) :
    translation (x ⊔ y) = translation x ⊔ translation y :=
  map_sup translation x y

/-- Negation reverses the ordered pair zero and one. -/
theorem negation_not_monotone : ¬ Monotone (fun z : Int => -z) := by
  intro h
  have reversal := h (show (0 : Int) ≤ 1 by norm_num)
  norm_num at reversal

#print axioms translation
#print axioms translation_apply
#print axioms translation_symm_apply
#print axioms transport
#print axioms transport_symm_transport
#print axioms transport_transport_symm
#print axioms transport_translation
#print axioms translation_recovers
#print axioms gap_translation
#print axioms translation_preserves_strictness
#print axioms selected_translation
#print axioms selected_strict
#print axioms selected_gap
#print axioms selected_recovers
#print axioms translation_nonidentity
#print axioms translation_inf
#print axioms translation_sup
#print axioms negation_not_monotone

end DirectTrial692
````

## attempt-01/Direct.lean

SHA-256: `fd79344645c4d95ef302737fff8e61e2617318e6b280e8c072f62dda66d40504`

````text
import Mathlib.Order.Hom.Lattice
import Mathlib.Tactic

namespace DirectTrial692

/-- Integer translation by three, with the specified inverse. -/
def translation : Int ≃o Int where
  toFun z := z + 3
  invFun z := z - 3
  left_inv z := by omega
  right_inv z := by omega
  map_rel_iff' := by intro a b; omega

@[simp] theorem translation_apply (z : Int) : translation z = z + 3 := rfl
@[simp] theorem translation_symm_apply (z : Int) : translation.symm z = z - 3 := rfl

/-- An ordered pair together with its order witness. -/
def OrderedPair := { p : Int × Int // p.1 ≤ p.2 }

/-- Transport the full dependent value through an ordinary order isomorphism. -/
def transport (e : Int ≃o Int) (p : OrderedPair) : OrderedPair :=
  ⟨(e p.val.1, e p.val.2), e.monotone p.property⟩

theorem transport_symm_transport (e : Int ≃o Int) (p : OrderedPair) :
    transport e.symm (transport e p) = p := by
  apply Subtype.ext
  apply Prod.ext <;> simp [transport]

theorem transport_transport_symm (e : Int ≃o Int) (p : OrderedPair) :
    transport e (transport e.symm p) = p := by
  apply Subtype.ext
  apply Prod.ext <;> simp [transport]

/-- The complete translated subtype value for arbitrary ordered endpoints. -/
theorem transport_translation (x y : Int) (h : x ≤ y) :
    transport translation ⟨(x, y), h⟩ =
      (⟨(x + 3, y + 3), by omega⟩ : OrderedPair) := by
  apply Subtype.ext
  rfl

/-- Recovery includes the order witness, through equality of subtype values. -/
theorem translation_recovers (x y : Int) (h : x ≤ y) :
    transport translation.symm (transport translation ⟨(x, y), h⟩) =
      (⟨(x, y), h⟩ : OrderedPair) :=
  transport_symm_transport translation _

def gap (p : OrderedPair) : Int := p.val.2 - p.val.1

theorem gap_translation (p : OrderedPair) :
    gap (transport translation p) = gap p := by
  change (p.val.2 + 3) - (p.val.1 + 3) = p.val.2 - p.val.1
  omega

theorem translation_preserves_strictness (p : OrderedPair)
    (h : p.val.1 < p.val.2) :
    (transport translation p).val.1 < (transport translation p).val.2 :=
  translation.strictMono h

def selected : OrderedPair := ⟨(-2, 4), by norm_num⟩

theorem selected_translation :
    transport translation selected = (⟨(1, 7), by norm_num⟩ : OrderedPair) := by
  apply Subtype.ext
  norm_num [transport, selected]

theorem selected_strict :
    (transport translation selected).val.1 <
      (transport translation selected).val.2 :=
  translation_preserves_strictness selected (by norm_num [selected])

theorem selected_gap : gap (transport translation selected) = 6 := by
  rw [gap_translation]
  norm_num [gap, selected]

theorem selected_recovers :
    transport translation.symm (transport translation selected) = selected :=
  transport_symm_transport translation selected

theorem translation_nonidentity : translation 0 = 3 ∧ translation 0 ≠ 0 := by
  norm_num

theorem translation_inf (x y : Int) :
    translation (x ⊓ y) = translation x ⊓ translation y :=
  map_inf translation x y

theorem translation_sup (x y : Int) :
    translation (x ⊔ y) = translation x ⊔ translation y :=
  map_sup translation x y

/-- Negation reverses the ordered pair zero and one. -/
theorem negation_not_monotone : ¬ Monotone (fun z : Int => -z) := by
  intro h
  have reversal := h (show (0 : Int) ≤ 1 by norm_num)
  norm_num at reversal

#print axioms translation
#print axioms translation_apply
#print axioms translation_symm_apply
#print axioms transport
#print axioms transport_symm_transport
#print axioms transport_transport_symm
#print axioms transport_translation
#print axioms translation_recovers
#print axioms gap_translation
#print axioms translation_preserves_strictness
#print axioms selected_translation
#print axioms selected_strict
#print axioms selected_gap
#print axioms selected_recovers
#print axioms translation_nonidentity
#print axioms translation_inf
#print axioms translation_sup
#print axioms negation_not_monotone

end DirectTrial692
````

## attempt-01/metrics.json

SHA-256: `a3ad0a80bbd9151feb82d151239ab65cb9086afc6ff8b3c28f32fa170755a211`

````text
{
  "index": 1,
  "command": [
    "direnv",
    "exec",
    "/home/vlad/Code/conaled",
    "lake",
    "env",
    "lean",
    "-EhasSorry",
    "-o",
    "/tmp/conaled-692-evidence/direct/Direct.olean",
    "/tmp/conaled-692-evidence/direct/Direct.lean"
  ],
  "source_sha256": "fd79344645c4d95ef302737fff8e61e2617318e6b280e8c072f62dda66d40504",
  "utc_before_lock": "2026-11-24T00:13:51.538450+00:00",
  "monotonic_before_lock": 107200.108815061,
  "lock_wait_seconds": 2.21920054173097e-05,
  "utc_start": "2026-11-24T00:13:51.538484+00:00",
  "monotonic_start": 107200.108842867,
  "exit_status": 1,
  "timed_out": false,
  "monotonic_end": 107200.674835909,
  "process_wall_seconds": 0.5659930419933517,
  "utc_end": "2026-11-24T00:13:52.104494+00:00",
  "user_seconds": 0.231241,
  "system_seconds": 0.302374,
  "peak_rss_kib": 799312
}
````

## attempt-01/stderr.log

SHA-256: `0039eb86d2c4aa3df4fd81724303476a45a6cab4ce60f0365ad611946678d8d8`

````text
[0mdirenv: loading ~/Code/conaled/.envrc
[0mdirenv: using flake
[0mdirenv: nix-direnv: Using cached dev shell
input file '/tmp/conaled-692-evidence/direct/Direct.lean' must be contained in root directory (/home/vlad/Code/conaled/)
````

## attempt-01/stdout.log

SHA-256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`

````text

````

## attempt-02/Direct.lean

SHA-256: `fd79344645c4d95ef302737fff8e61e2617318e6b280e8c072f62dda66d40504`

````text
import Mathlib.Order.Hom.Lattice
import Mathlib.Tactic

namespace DirectTrial692

/-- Integer translation by three, with the specified inverse. -/
def translation : Int ≃o Int where
  toFun z := z + 3
  invFun z := z - 3
  left_inv z := by omega
  right_inv z := by omega
  map_rel_iff' := by intro a b; omega

@[simp] theorem translation_apply (z : Int) : translation z = z + 3 := rfl
@[simp] theorem translation_symm_apply (z : Int) : translation.symm z = z - 3 := rfl

/-- An ordered pair together with its order witness. -/
def OrderedPair := { p : Int × Int // p.1 ≤ p.2 }

/-- Transport the full dependent value through an ordinary order isomorphism. -/
def transport (e : Int ≃o Int) (p : OrderedPair) : OrderedPair :=
  ⟨(e p.val.1, e p.val.2), e.monotone p.property⟩

theorem transport_symm_transport (e : Int ≃o Int) (p : OrderedPair) :
    transport e.symm (transport e p) = p := by
  apply Subtype.ext
  apply Prod.ext <;> simp [transport]

theorem transport_transport_symm (e : Int ≃o Int) (p : OrderedPair) :
    transport e (transport e.symm p) = p := by
  apply Subtype.ext
  apply Prod.ext <;> simp [transport]

/-- The complete translated subtype value for arbitrary ordered endpoints. -/
theorem transport_translation (x y : Int) (h : x ≤ y) :
    transport translation ⟨(x, y), h⟩ =
      (⟨(x + 3, y + 3), by omega⟩ : OrderedPair) := by
  apply Subtype.ext
  rfl

/-- Recovery includes the order witness, through equality of subtype values. -/
theorem translation_recovers (x y : Int) (h : x ≤ y) :
    transport translation.symm (transport translation ⟨(x, y), h⟩) =
      (⟨(x, y), h⟩ : OrderedPair) :=
  transport_symm_transport translation _

def gap (p : OrderedPair) : Int := p.val.2 - p.val.1

theorem gap_translation (p : OrderedPair) :
    gap (transport translation p) = gap p := by
  change (p.val.2 + 3) - (p.val.1 + 3) = p.val.2 - p.val.1
  omega

theorem translation_preserves_strictness (p : OrderedPair)
    (h : p.val.1 < p.val.2) :
    (transport translation p).val.1 < (transport translation p).val.2 :=
  translation.strictMono h

def selected : OrderedPair := ⟨(-2, 4), by norm_num⟩

theorem selected_translation :
    transport translation selected = (⟨(1, 7), by norm_num⟩ : OrderedPair) := by
  apply Subtype.ext
  norm_num [transport, selected]

theorem selected_strict :
    (transport translation selected).val.1 <
      (transport translation selected).val.2 :=
  translation_preserves_strictness selected (by norm_num [selected])

theorem selected_gap : gap (transport translation selected) = 6 := by
  rw [gap_translation]
  norm_num [gap, selected]

theorem selected_recovers :
    transport translation.symm (transport translation selected) = selected :=
  transport_symm_transport translation selected

theorem translation_nonidentity : translation 0 = 3 ∧ translation 0 ≠ 0 := by
  norm_num

theorem translation_inf (x y : Int) :
    translation (x ⊓ y) = translation x ⊓ translation y :=
  map_inf translation x y

theorem translation_sup (x y : Int) :
    translation (x ⊔ y) = translation x ⊔ translation y :=
  map_sup translation x y

/-- Negation reverses the ordered pair zero and one. -/
theorem negation_not_monotone : ¬ Monotone (fun z : Int => -z) := by
  intro h
  have reversal := h (show (0 : Int) ≤ 1 by norm_num)
  norm_num at reversal

#print axioms translation
#print axioms translation_apply
#print axioms translation_symm_apply
#print axioms transport
#print axioms transport_symm_transport
#print axioms transport_transport_symm
#print axioms transport_translation
#print axioms translation_recovers
#print axioms gap_translation
#print axioms translation_preserves_strictness
#print axioms selected_translation
#print axioms selected_strict
#print axioms selected_gap
#print axioms selected_recovers
#print axioms translation_nonidentity
#print axioms translation_inf
#print axioms translation_sup
#print axioms negation_not_monotone

end DirectTrial692
````

## attempt-02/metrics.json

SHA-256: `bcc7a59f2f257eae04d580b4bc1f29f3865662d028e9a0e3fcdded61dd6f6c5d`

````text
{
  "index": 2,
  "command": [
    "direnv",
    "exec",
    "/home/vlad/Code/conaled",
    "lake",
    "env",
    "lean",
    "-EhasSorry",
    "--root",
    "/tmp/conaled-692-evidence/direct",
    "-o",
    "/tmp/conaled-692-evidence/direct/Direct.olean",
    "/tmp/conaled-692-evidence/direct/Direct.lean"
  ],
  "source_sha256": "fd79344645c4d95ef302737fff8e61e2617318e6b280e8c072f62dda66d40504",
  "utc_before_lock": "2026-11-24T00:13:57.709427+00:00",
  "monotonic_before_lock": 107206.279789193,
  "lock_wait_seconds": 1.0767005733214319e-05,
  "utc_start": "2026-11-24T00:13:57.709446+00:00",
  "monotonic_start": 107206.279802911,
  "exit_status": 1,
  "timed_out": false,
  "monotonic_end": 107207.847258261,
  "process_wall_seconds": 1.5674553499993635,
  "utc_end": "2026-11-24T00:13:59.276910+00:00",
  "user_seconds": 1.233802,
  "system_seconds": 0.611014,
  "peak_rss_kib": 3423644
}
````

## attempt-02/stderr.log

SHA-256: `f24710937e102e96b6b94c56a3c230c346e46a7a5b2efa7cd874c7e1b3057eaf`

````text
[0mdirenv: loading ~/Code/conaled/.envrc
[0mdirenv: using flake
[0mdirenv: nix-direnv: Using cached dev shell
````

## attempt-02/stdout.log

SHA-256: `edc79e7ea9d69593af3c26e3e6e156a5c3610e8ff9b4296e54c3e2c3b0b36b37`

````text
/tmp/conaled-692-evidence/direct/Direct.lean:10:19: error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  a - b ≥ 1
where
 a := z
 b := (fun z => z - 3) ((fun z => z + 3) z)
/tmp/conaled-692-evidence/direct/Direct.lean:11:20: error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  a - b ≥ 1
where
 a := z
 b := (fun z => z + 3) ((fun z => z - 3) z)
'DirectTrial692.translation' depends on axioms: [sorryAx, Quot.sound]
'DirectTrial692.translation_apply' depends on axioms: [sorryAx, Quot.sound]
'DirectTrial692.translation_symm_apply' depends on axioms: [propext, sorryAx, Quot.sound]
'DirectTrial692.transport' depends on axioms: [propext, Quot.sound]
'DirectTrial692.transport_symm_transport' depends on axioms: [propext, Quot.sound]
'DirectTrial692.transport_transport_symm' depends on axioms: [propext, Quot.sound]
'DirectTrial692.transport_translation' depends on axioms: [propext, sorryAx, Quot.sound]
'DirectTrial692.translation_recovers' depends on axioms: [propext, sorryAx, Quot.sound]
'DirectTrial692.gap_translation' depends on axioms: [propext, sorryAx, Quot.sound]
'DirectTrial692.translation_preserves_strictness' depends on axioms: [propext, sorryAx, Quot.sound]
'DirectTrial692.selected_translation' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'DirectTrial692.selected_strict' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'DirectTrial692.selected_gap' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'DirectTrial692.selected_recovers' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'DirectTrial692.translation_nonidentity' depends on axioms: [propext, sorryAx, Quot.sound]
'DirectTrial692.translation_inf' depends on axioms: [propext, sorryAx, Quot.sound]
'DirectTrial692.translation_sup' depends on axioms: [propext, sorryAx, Quot.sound]
'DirectTrial692.negation_not_monotone' depends on axioms: [propext, Classical.choice, Quot.sound]
````

## attempt-03/Direct.lean

SHA-256: `5b78a5ccd35f02580cd22476f9d9ec2506d6dcc1b80ec37ffe49e038002a8e11`

````text
import Mathlib.Order.Hom.Lattice
import Mathlib.Tactic

namespace DirectTrial692

/-- Integer translation by three, with the specified inverse. -/
def translation : Int ≃o Int where
  toFun z := z + 3
  invFun z := z - 3
  left_inv z := by change (z + 3) - 3 = z; omega
  right_inv z := by change (z - 3) + 3 = z; omega
  map_rel_iff' := by intro a b; omega

@[simp] theorem translation_apply (z : Int) : translation z = z + 3 := rfl
@[simp] theorem translation_symm_apply (z : Int) : translation.symm z = z - 3 := rfl

/-- An ordered pair together with its order witness. -/
def OrderedPair := { p : Int × Int // p.1 ≤ p.2 }

/-- Transport the full dependent value through an ordinary order isomorphism. -/
def transport (e : Int ≃o Int) (p : OrderedPair) : OrderedPair :=
  ⟨(e p.val.1, e p.val.2), e.monotone p.property⟩

theorem transport_symm_transport (e : Int ≃o Int) (p : OrderedPair) :
    transport e.symm (transport e p) = p := by
  apply Subtype.ext
  apply Prod.ext <;> simp [transport]

theorem transport_transport_symm (e : Int ≃o Int) (p : OrderedPair) :
    transport e (transport e.symm p) = p := by
  apply Subtype.ext
  apply Prod.ext <;> simp [transport]

/-- The complete translated subtype value for arbitrary ordered endpoints. -/
theorem transport_translation (x y : Int) (h : x ≤ y) :
    transport translation ⟨(x, y), h⟩ =
      (⟨(x + 3, y + 3), by omega⟩ : OrderedPair) := by
  apply Subtype.ext
  rfl

/-- Recovery includes the order witness, through equality of subtype values. -/
theorem translation_recovers (x y : Int) (h : x ≤ y) :
    transport translation.symm (transport translation ⟨(x, y), h⟩) =
      (⟨(x, y), h⟩ : OrderedPair) :=
  transport_symm_transport translation _

def gap (p : OrderedPair) : Int := p.val.2 - p.val.1

theorem gap_translation (p : OrderedPair) :
    gap (transport translation p) = gap p := by
  change (p.val.2 + 3) - (p.val.1 + 3) = p.val.2 - p.val.1
  omega

theorem translation_preserves_strictness (p : OrderedPair)
    (h : p.val.1 < p.val.2) :
    (transport translation p).val.1 < (transport translation p).val.2 :=
  translation.strictMono h

def selected : OrderedPair := ⟨(-2, 4), by norm_num⟩

theorem selected_translation :
    transport translation selected = (⟨(1, 7), by norm_num⟩ : OrderedPair) := by
  apply Subtype.ext
  norm_num [transport, selected]

theorem selected_strict :
    (transport translation selected).val.1 <
      (transport translation selected).val.2 :=
  translation_preserves_strictness selected (by norm_num [selected])

theorem selected_gap : gap (transport translation selected) = 6 := by
  rw [gap_translation]
  norm_num [gap, selected]

theorem selected_recovers :
    transport translation.symm (transport translation selected) = selected :=
  transport_symm_transport translation selected

theorem translation_nonidentity : translation 0 = 3 ∧ translation 0 ≠ 0 := by
  norm_num

theorem translation_inf (x y : Int) :
    translation (x ⊓ y) = translation x ⊓ translation y :=
  map_inf translation x y

theorem translation_sup (x y : Int) :
    translation (x ⊔ y) = translation x ⊔ translation y :=
  map_sup translation x y

/-- Negation reverses the ordered pair zero and one. -/
theorem negation_not_monotone : ¬ Monotone (fun z : Int => -z) := by
  intro h
  have reversal := h (show (0 : Int) ≤ 1 by norm_num)
  norm_num at reversal

#print axioms translation
#print axioms translation_apply
#print axioms translation_symm_apply
#print axioms transport
#print axioms transport_symm_transport
#print axioms transport_transport_symm
#print axioms transport_translation
#print axioms translation_recovers
#print axioms gap_translation
#print axioms translation_preserves_strictness
#print axioms selected_translation
#print axioms selected_strict
#print axioms selected_gap
#print axioms selected_recovers
#print axioms translation_nonidentity
#print axioms translation_inf
#print axioms translation_sup
#print axioms negation_not_monotone

end DirectTrial692
````

## attempt-03/metrics.json

SHA-256: `be884f4eae230c8a13c6fd0099100cf12d752e09e3ab2a35ba48105411eb81db`

````text
{
  "index": 3,
  "command": [
    "direnv",
    "exec",
    "/home/vlad/Code/conaled",
    "lake",
    "env",
    "lean",
    "-EhasSorry",
    "--root",
    "/tmp/conaled-692-evidence/direct",
    "-o",
    "/tmp/conaled-692-evidence/direct/Direct.olean",
    "/tmp/conaled-692-evidence/direct/Direct.lean"
  ],
  "source_sha256": "5b78a5ccd35f02580cd22476f9d9ec2506d6dcc1b80ec37ffe49e038002a8e11",
  "utc_before_lock": "2026-11-24T00:14:06.231878+00:00",
  "monotonic_before_lock": 107214.80223879,
  "lock_wait_seconds": 1.0867006494663656e-05,
  "utc_start": "2026-11-24T00:14:06.231895+00:00",
  "monotonic_start": 107214.802252055,
  "exit_status": 1,
  "timed_out": false,
  "monotonic_end": 107216.520991585,
  "process_wall_seconds": 1.7187395299988566,
  "utc_end": "2026-11-24T00:14:07.950641+00:00",
  "user_seconds": 1.3023,
  "system_seconds": 0.7045269999999999,
  "peak_rss_kib": 3423844
}
````

## attempt-03/stderr.log

SHA-256: `f24710937e102e96b6b94c56a3c230c346e46a7a5b2efa7cd874c7e1b3057eaf`

````text
[0mdirenv: loading ~/Code/conaled/.envrc
[0mdirenv: using flake
[0mdirenv: nix-direnv: Using cached dev shell
````

## attempt-03/stdout.log

SHA-256: `e1d82bdc3755b23ad0bbb056a642024451424c4bd729f15e8ab2dbd54c410263`

````text
/tmp/conaled-692-evidence/direct/Direct.lean:12:32: error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  e - f ≥ 1
  c - d ≥ 0
where
 c := { toFun := fun z => z + 3, invFun := fun z => z - 3, left_inv := ⋯, right_inv := ⋯ } b
 d := { toFun := fun z => z + 3, invFun := fun z => z - 3, left_inv := ⋯, right_inv := ⋯ } a
 e := a
 f := b
'DirectTrial692.translation' depends on axioms: [propext, sorryAx, Quot.sound]
'DirectTrial692.translation_apply' depends on axioms: [propext, sorryAx, Quot.sound]
'DirectTrial692.translation_symm_apply' depends on axioms: [propext, sorryAx, Quot.sound]
'DirectTrial692.transport' depends on axioms: [propext, Quot.sound]
'DirectTrial692.transport_symm_transport' depends on axioms: [propext, Quot.sound]
'DirectTrial692.transport_transport_symm' depends on axioms: [propext, Quot.sound]
'DirectTrial692.transport_translation' depends on axioms: [propext, sorryAx, Quot.sound]
'DirectTrial692.translation_recovers' depends on axioms: [propext, sorryAx, Quot.sound]
'DirectTrial692.gap_translation' depends on axioms: [propext, sorryAx, Quot.sound]
'DirectTrial692.translation_preserves_strictness' depends on axioms: [propext, sorryAx, Quot.sound]
'DirectTrial692.selected_translation' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'DirectTrial692.selected_strict' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'DirectTrial692.selected_gap' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'DirectTrial692.selected_recovers' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'DirectTrial692.translation_nonidentity' depends on axioms: [propext, sorryAx, Quot.sound]
'DirectTrial692.translation_inf' depends on axioms: [propext, sorryAx, Quot.sound]
'DirectTrial692.translation_sup' depends on axioms: [propext, sorryAx, Quot.sound]
'DirectTrial692.negation_not_monotone' depends on axioms: [propext, Classical.choice, Quot.sound]
````

## attempt-04/Direct.lean

SHA-256: `cfb3f939980dd34ec20a067e3c3ffb67fc1710712466a04098c54ff5f4ef794c`

````text
import Mathlib.Order.Hom.Lattice
import Mathlib.Tactic

namespace DirectTrial692

/-- Integer translation by three, with the specified inverse. -/
def translation : Int ≃o Int where
  toFun z := z + 3
  invFun z := z - 3
  left_inv z := by change (z + 3) - 3 = z; omega
  right_inv z := by change (z - 3) + 3 = z; omega
  map_rel_iff' := by intro a b; change (a + 3 ≤ b + 3) ↔ a ≤ b; omega

@[simp] theorem translation_apply (z : Int) : translation z = z + 3 := rfl
@[simp] theorem translation_symm_apply (z : Int) : translation.symm z = z - 3 := rfl

/-- An ordered pair together with its order witness. -/
def OrderedPair := { p : Int × Int // p.1 ≤ p.2 }

/-- Transport the full dependent value through an ordinary order isomorphism. -/
def transport (e : Int ≃o Int) (p : OrderedPair) : OrderedPair :=
  ⟨(e p.val.1, e p.val.2), e.monotone p.property⟩

theorem transport_symm_transport (e : Int ≃o Int) (p : OrderedPair) :
    transport e.symm (transport e p) = p := by
  apply Subtype.ext
  apply Prod.ext <;> simp [transport]

theorem transport_transport_symm (e : Int ≃o Int) (p : OrderedPair) :
    transport e (transport e.symm p) = p := by
  apply Subtype.ext
  apply Prod.ext <;> simp [transport]

/-- The complete translated subtype value for arbitrary ordered endpoints. -/
theorem transport_translation (x y : Int) (h : x ≤ y) :
    transport translation ⟨(x, y), h⟩ =
      (⟨(x + 3, y + 3), by omega⟩ : OrderedPair) := by
  apply Subtype.ext
  rfl

/-- Recovery includes the order witness, through equality of subtype values. -/
theorem translation_recovers (x y : Int) (h : x ≤ y) :
    transport translation.symm (transport translation ⟨(x, y), h⟩) =
      (⟨(x, y), h⟩ : OrderedPair) :=
  transport_symm_transport translation _

def gap (p : OrderedPair) : Int := p.val.2 - p.val.1

theorem gap_translation (p : OrderedPair) :
    gap (transport translation p) = gap p := by
  change (p.val.2 + 3) - (p.val.1 + 3) = p.val.2 - p.val.1
  omega

theorem translation_preserves_strictness (p : OrderedPair)
    (h : p.val.1 < p.val.2) :
    (transport translation p).val.1 < (transport translation p).val.2 :=
  translation.strictMono h

def selected : OrderedPair := ⟨(-2, 4), by norm_num⟩

theorem selected_translation :
    transport translation selected = (⟨(1, 7), by norm_num⟩ : OrderedPair) := by
  apply Subtype.ext
  norm_num [transport, selected]

theorem selected_strict :
    (transport translation selected).val.1 <
      (transport translation selected).val.2 :=
  translation_preserves_strictness selected (by norm_num [selected])

theorem selected_gap : gap (transport translation selected) = 6 := by
  rw [gap_translation]
  norm_num [gap, selected]

theorem selected_recovers :
    transport translation.symm (transport translation selected) = selected :=
  transport_symm_transport translation selected

theorem translation_nonidentity : translation 0 = 3 ∧ translation 0 ≠ 0 := by
  norm_num

theorem translation_inf (x y : Int) :
    translation (x ⊓ y) = translation x ⊓ translation y :=
  map_inf translation x y

theorem translation_sup (x y : Int) :
    translation (x ⊔ y) = translation x ⊔ translation y :=
  map_sup translation x y

/-- Negation reverses the ordered pair zero and one. -/
theorem negation_not_monotone : ¬ Monotone (fun z : Int => -z) := by
  intro h
  have reversal := h (show (0 : Int) ≤ 1 by norm_num)
  norm_num at reversal

#print axioms translation
#print axioms translation_apply
#print axioms translation_symm_apply
#print axioms transport
#print axioms transport_symm_transport
#print axioms transport_transport_symm
#print axioms transport_translation
#print axioms translation_recovers
#print axioms gap_translation
#print axioms translation_preserves_strictness
#print axioms selected_translation
#print axioms selected_strict
#print axioms selected_gap
#print axioms selected_recovers
#print axioms translation_nonidentity
#print axioms translation_inf
#print axioms translation_sup
#print axioms negation_not_monotone

end DirectTrial692
````

## attempt-04/metrics.json

SHA-256: `55fc5c6f95a89886fb890183eb5f943ae92bdb5a0eef0bfce2ea68459ce59794`

````text
{
  "index": 4,
  "command": [
    "direnv",
    "exec",
    "/home/vlad/Code/conaled",
    "lake",
    "env",
    "lean",
    "-EhasSorry",
    "--root",
    "/tmp/conaled-692-evidence/direct",
    "-o",
    "/tmp/conaled-692-evidence/direct/Direct.olean",
    "/tmp/conaled-692-evidence/direct/Direct.lean"
  ],
  "source_sha256": "cfb3f939980dd34ec20a067e3c3ffb67fc1710712466a04098c54ff5f4ef794c",
  "utc_before_lock": "2026-11-24T00:14:16.027808+00:00",
  "monotonic_before_lock": 107224.598169687,
  "lock_wait_seconds": 9.747003787197173e-06,
  "utc_start": "2026-11-24T00:14:16.027825+00:00",
  "monotonic_start": 107224.59818165,
  "exit_status": 0,
  "timed_out": false,
  "monotonic_end": 107226.317162446,
  "process_wall_seconds": 1.7189807959948666,
  "utc_end": "2026-11-24T00:14:17.746811+00:00",
  "user_seconds": 1.323625,
  "system_seconds": 0.659682,
  "peak_rss_kib": 3435348
}
````

## attempt-04/stderr.log

SHA-256: `f24710937e102e96b6b94c56a3c230c346e46a7a5b2efa7cd874c7e1b3057eaf`

````text
[0mdirenv: loading ~/Code/conaled/.envrc
[0mdirenv: using flake
[0mdirenv: nix-direnv: Using cached dev shell
````

## attempt-04/stdout.log

SHA-256: `2e1680668558c17390bf9f17d385716b8e0b4a0316c3513e0b46ffaaa2ae41cd`

````text
'DirectTrial692.translation' depends on axioms: [propext, Classical.choice, Quot.sound]
'DirectTrial692.translation_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'DirectTrial692.translation_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'DirectTrial692.transport' depends on axioms: [propext, Quot.sound]
'DirectTrial692.transport_symm_transport' depends on axioms: [propext, Quot.sound]
'DirectTrial692.transport_transport_symm' depends on axioms: [propext, Quot.sound]
'DirectTrial692.transport_translation' depends on axioms: [propext, Classical.choice, Quot.sound]
'DirectTrial692.translation_recovers' depends on axioms: [propext, Classical.choice, Quot.sound]
'DirectTrial692.gap_translation' depends on axioms: [propext, Classical.choice, Quot.sound]
'DirectTrial692.translation_preserves_strictness' depends on axioms: [propext, Classical.choice, Quot.sound]
'DirectTrial692.selected_translation' depends on axioms: [propext, Classical.choice, Quot.sound]
'DirectTrial692.selected_strict' depends on axioms: [propext, Classical.choice, Quot.sound]
'DirectTrial692.selected_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'DirectTrial692.selected_recovers' depends on axioms: [propext, Classical.choice, Quot.sound]
'DirectTrial692.translation_nonidentity' depends on axioms: [propext, Classical.choice, Quot.sound]
'DirectTrial692.translation_inf' depends on axioms: [propext, Classical.choice, Quot.sound]
'DirectTrial692.translation_sup' depends on axioms: [propext, Classical.choice, Quot.sound]
'DirectTrial692.negation_not_monotone' depends on axioms: [propext, Classical.choice, Quot.sound]
````

## environment-events.log

SHA-256: `c28a5d56915c3379c9bcc9dc46c3b802f39bc1062eb79d64f66136fe47161e4c`

````text
Transcribed from the tool transcript; this event occurred before Lean invocation 1.
Command: python3 /tmp/conaled-692-evidence/direct/run.py
Exit status: 127
Output: /run/current-system/sw/bin/bash: line 165: python3: command not found
Resolution: invoke the runner with direnv exec . python3, as prescribed by the repository environment instructions.
No Lean process started for this failed command. The source and runner files had already been written.
````

## invocations.json

SHA-256: `c43f97a17917afe62e7133d85ae53ccff389cc57a8df776b5eda2ec1a01bc7ae`

````text
[
  {
    "index": 1,
    "command": [
      "direnv",
      "exec",
      "/home/vlad/Code/conaled",
      "lake",
      "env",
      "lean",
      "-EhasSorry",
      "-o",
      "/tmp/conaled-692-evidence/direct/Direct.olean",
      "/tmp/conaled-692-evidence/direct/Direct.lean"
    ],
    "source_sha256": "fd79344645c4d95ef302737fff8e61e2617318e6b280e8c072f62dda66d40504",
    "utc_before_lock": "2026-11-24T00:13:51.538450+00:00",
    "monotonic_before_lock": 107200.108815061,
    "lock_wait_seconds": 2.21920054173097e-05,
    "utc_start": "2026-11-24T00:13:51.538484+00:00",
    "monotonic_start": 107200.108842867,
    "exit_status": 1,
    "timed_out": false,
    "monotonic_end": 107200.674835909,
    "process_wall_seconds": 0.5659930419933517,
    "utc_end": "2026-11-24T00:13:52.104494+00:00",
    "user_seconds": 0.231241,
    "system_seconds": 0.302374,
    "peak_rss_kib": 799312
  },
  {
    "index": 2,
    "command": [
      "direnv",
      "exec",
      "/home/vlad/Code/conaled",
      "lake",
      "env",
      "lean",
      "-EhasSorry",
      "--root",
      "/tmp/conaled-692-evidence/direct",
      "-o",
      "/tmp/conaled-692-evidence/direct/Direct.olean",
      "/tmp/conaled-692-evidence/direct/Direct.lean"
    ],
    "source_sha256": "fd79344645c4d95ef302737fff8e61e2617318e6b280e8c072f62dda66d40504",
    "utc_before_lock": "2026-11-24T00:13:57.709427+00:00",
    "monotonic_before_lock": 107206.279789193,
    "lock_wait_seconds": 1.0767005733214319e-05,
    "utc_start": "2026-11-24T00:13:57.709446+00:00",
    "monotonic_start": 107206.279802911,
    "exit_status": 1,
    "timed_out": false,
    "monotonic_end": 107207.847258261,
    "process_wall_seconds": 1.5674553499993635,
    "utc_end": "2026-11-24T00:13:59.276910+00:00",
    "user_seconds": 1.233802,
    "system_seconds": 0.611014,
    "peak_rss_kib": 3423644
  },
  {
    "index": 3,
    "command": [
      "direnv",
      "exec",
      "/home/vlad/Code/conaled",
      "lake",
      "env",
      "lean",
      "-EhasSorry",
      "--root",
      "/tmp/conaled-692-evidence/direct",
      "-o",
      "/tmp/conaled-692-evidence/direct/Direct.olean",
      "/tmp/conaled-692-evidence/direct/Direct.lean"
    ],
    "source_sha256": "5b78a5ccd35f02580cd22476f9d9ec2506d6dcc1b80ec37ffe49e038002a8e11",
    "utc_before_lock": "2026-11-24T00:14:06.231878+00:00",
    "monotonic_before_lock": 107214.80223879,
    "lock_wait_seconds": 1.0867006494663656e-05,
    "utc_start": "2026-11-24T00:14:06.231895+00:00",
    "monotonic_start": 107214.802252055,
    "exit_status": 1,
    "timed_out": false,
    "monotonic_end": 107216.520991585,
    "process_wall_seconds": 1.7187395299988566,
    "utc_end": "2026-11-24T00:14:07.950641+00:00",
    "user_seconds": 1.3023,
    "system_seconds": 0.7045269999999999,
    "peak_rss_kib": 3423844
  },
  {
    "index": 4,
    "command": [
      "direnv",
      "exec",
      "/home/vlad/Code/conaled",
      "lake",
      "env",
      "lean",
      "-EhasSorry",
      "--root",
      "/tmp/conaled-692-evidence/direct",
      "-o",
      "/tmp/conaled-692-evidence/direct/Direct.olean",
      "/tmp/conaled-692-evidence/direct/Direct.lean"
    ],
    "source_sha256": "cfb3f939980dd34ec20a067e3c3ffb67fc1710712466a04098c54ff5f4ef794c",
    "utc_before_lock": "2026-11-24T00:14:16.027808+00:00",
    "monotonic_before_lock": 107224.598169687,
    "lock_wait_seconds": 9.747003787197173e-06,
    "utc_start": "2026-11-24T00:14:16.027825+00:00",
    "monotonic_start": 107224.59818165,
    "exit_status": 0,
    "timed_out": false,
    "monotonic_end": 107226.317162446,
    "process_wall_seconds": 1.7189807959948666,
    "utc_end": "2026-11-24T00:14:17.746811+00:00",
    "user_seconds": 1.323625,
    "system_seconds": 0.659682,
    "peak_rss_kib": 3435348
  }
]
````

## report.md

SHA-256: `290c77f47a4df7b3f0897411bb5e1e3c4eb9b61af576c1ea45c03f1c9237cf51`

````text
# Direct author trial #692

The direct route succeeded. `Direct.lean` checked at 2026-11-24
00:14:17.746811 UTC and emitted `Direct.olean` outside the repository. Proof work
stopped at that first successful check. No later source changes or Lean
invocations were made.

The frozen protocol SHA-256 is
`fd834e2f03128c234ad9d493afc4f43237c62af300a663a5def32a16a4d19377`.
The checkout remained at `a38e05358d47f1739aa2f1fbcae8f9cc0d120f86`.
Final source SHA-256:
`cfb3f939980dd34ec20a067e3c3ffb67fc1710712466a04098c54ff5f4ef794c`.
Final olean SHA-256:
`04878fd5e9b958e5230f679071561aeee1dda0b25155d5a99aa6208fe6a15c1a`.

## Checked task and statement review

`translation : Int ≃o Int` sends every integer to itself plus three and has
inverse subtraction of three. Both inverse laws and order reflection are
proved by integer arithmetic. `translation_apply` and
`translation_symm_apply` expose those functions explicitly.

`OrderedPair` is the subtype of `Int × Int` satisfying first ≤ second.
`transport` maps both coordinates through an arbitrary ordinary `OrderIso`
and carries its monotonicity proof. `transport_translation` gives the entire
translated subtype value for arbitrary `x`, `y` and `h : x ≤ y`.
`transport_symm_transport` and `transport_transport_symm` prove equality of
whole dependent values in both directions. `translation_recovers` specializes
the first result to the requested arbitrary ordered integer pair. The proofs
use subtype extensionality, so the equalities include the proof component
under Lean's proof irrelevance, rather than projecting only coordinates.

`gap_translation` proves invariance of second minus first for every ordered
pair. `translation_preserves_strictness` derives strict preservation from the
same order isomorphism. The selected input `(-2,4)` has a proved order witness;
`selected_translation` proves its whole translated value equals `(1,7)` with
its order witness. `selected_strict`, `selected_gap` and `selected_recovers`
consume the general results to show strictness, gap six and whole recovery.
`translation_nonidentity` proves `translation 0 = 3` and `translation 0 ≠ 0`.

`translation_inf` and `translation_sup` quantify over all integers and use
Mathlib's lattice preservation laws for the same order isomorphism.
`negation_not_monotone` refutes ordinary integer monotonicity by applying a
hypothetical monotonicity proof to `0 ≤ 1`, obtaining the false inequality
`0 ≤ -1`. This is a proved rejecting control, not an unsuccessful encoding.

These statements have the intended types, directions and universal scope.
The ordered-pair hypothesis is satisfied by the selected strict pair. Gap
preservation is specific to translation, not claimed for arbitrary order
isomorphisms. No native lattice API or native-model contract was attempted;
those are outside the direct route.

## Attempts and assistance

The first shell attempt to launch the Python measurement runner lacked Python
on the outer shell PATH. No Lean process started. The event is transcribed in
`environment-events.log`. Running the wrapper through `direnv exec .` fixed it.

1. Lean invocation 1 failed because an external input file requires an explicit
   `--root` for external olean emission. The source was unchanged for invocation 2.
2. Invocation 2 reached elaboration, but `omega` did not reduce the lambda
   applications in the inverse-law fields. Explicit `change` statements exposed
   the integer arithmetic.
3. Invocation 3 exposed the analogous reduction issue in `map_rel_iff'`.
   An explicit arithmetic `change` resolved it.
4. Invocation 4 checked every declaration successfully. Its axiom listings use
   only `propext`, `Classical.choice` and `Quot.sound`.

The failed checks contain Lean-generated `sorryAx` dependencies for failed
proofs; their error status and logs are retained. No source uses `sorry`,
`admit`, a new axiom, native evaluation, or a kernel bypass. No recursion-depth
or heartbeat options were changed from the defaults.

Read-only inputs were the frozen protocol, task assignment, applicable
repository guidance, and a search of pinned Mathlib's `Order/Hom/Lattice.lean`
for its `map_inf` and `map_sup` interfaces. No native implementation, sibling
attempt or native research report was inspected. No web access, subagent,
external proof help or API hint was used. The sole clarification to the
orchestrator concerned the missing exact assignment timestamp; the response
confirmed it had not been recorded and asked for conservative accounting.
The model/effort selection is as relayed in the assignment and protocol;
host runtime details were not inspected or self-attested.

## Timing and retained evidence

The exact assignment timestamp was not captured. The first local UTC clock
observation, after reading instructions, was 2026-11-24 00:12:41 UTC. Success
was reached about 96.75 seconds after that observation. This is a lower bound
on total author elapsed time because instruction reading preceded it; it must
not be presented as exact assignment-to-success duration. The attempt
completed well inside the 20-minute bound without extending the deadline.

`invocations.json` records each exact command, source hash, UTC start/end,
monotonic start/end, exit status, timeout flag, wall time, user/system CPU,
peak RSS and lock wait. Each `attempt-NN` directory contains the precompile
source snapshot, separate stdout/stderr and its metrics. CPU/RSS come from
Python child resource accounting; wall time includes the direnv/Lake launcher,
so it is a conservative measure of the Lean command. Lock waiting is recorded
separately. The 30-second timeout was never reached. No lock wait was material.

`run.py` is the measurement harness. Its current version includes the external
root correction; the manifest retains the exact earlier command. The source
snapshots retain every compiled version. The successful check includes axiom
listings for all theorem declarations and the main constructions. The normal
repository acceptance build was not run for this external author artifact;
integration and independent review remain the orchestrator's work.

This is one bounded agent-author observation. Prior library preparation in
#621/#691 is excluded from measured client effort, as specified by the
protocol. This result alone does not establish human productivity, general
route superiority or configuration approval.

Measured totals: 4 Lean commands, 5.571169 seconds cumulative command wall time, 4.090968 user seconds, 2.277597 system seconds, and 3435348 KiB maximum reported peak RSS. Machine-readable totals are in `summary.json`.
````

## run.py

SHA-256: `a2088ce904c7f7fc4b0f7ae1a0757dc388a4e85fb2da97427db98e2018c4b8dc`

````text
import datetime, fcntl, hashlib, json, pathlib, resource, shutil, subprocess, time
base = pathlib.Path('/tmp/conaled-692-evidence/direct')
manifest = base / 'invocations.json'
entries = json.loads(manifest.read_text()) if manifest.exists() else []
assert len(entries) < 25
assert sum(e['process_wall_seconds'] for e in entries) < 480
index = len(entries) + 1
attempt = base / f'attempt-{index:02d}'
attempt.mkdir()
source = base / 'Direct.lean'
shutil.copy2(source, attempt / 'Direct.lean')
cmd = ['direnv', 'exec', '/home/vlad/Code/conaled', 'lake', 'env', 'lean',
       '-EhasSorry', '--root', str(base), '-o', str(base / 'Direct.olean'), str(source)]
entry = {'index':index, 'command':cmd,
         'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
         'utc_before_lock':datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'monotonic_before_lock':time.monotonic()}
lock = open('/tmp/conaled-native-followups-lake.lock', 'a')
fcntl.flock(lock, fcntl.LOCK_EX)
entry['lock_wait_seconds'] = time.monotonic()-entry['monotonic_before_lock']
entry['utc_start'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
entry['monotonic_start'] = time.monotonic()
before = resource.getrusage(resource.RUSAGE_CHILDREN)
with (attempt / 'stdout.log').open('wb') as out, (attempt / 'stderr.log').open('wb') as err:
    try:
        result = subprocess.run(cmd, stdout=out, stderr=err, timeout=30,
                                cwd='/home/vlad/Code/conaled')
        entry['exit_status'] = result.returncode
        entry['timed_out'] = False
    except subprocess.TimeoutExpired:
        entry['exit_status'] = 124
        entry['timed_out'] = True
entry['monotonic_end'] = time.monotonic()
entry['process_wall_seconds'] = entry['monotonic_end']-entry['monotonic_start']
entry['utc_end'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
after = resource.getrusage(resource.RUSAGE_CHILDREN)
entry.update(user_seconds=after.ru_utime-before.ru_utime,
             system_seconds=after.ru_stime-before.ru_stime, peak_rss_kib=after.ru_maxrss)
fcntl.flock(lock, fcntl.LOCK_UN)
entries.append(entry)
manifest.write_text(json.dumps(entries, indent=2)+'\n')
(attempt / 'metrics.json').write_text(json.dumps(entry, indent=2)+'\n')
print(json.dumps(entry, indent=2))
print((attempt / 'stdout.log').read_text())
print((attempt / 'stderr.log').read_text())
````

## summary.json

SHA-256: `355b05970d1ba5308d3ceea7618fb28605b71b87a61cad4602f68ca3a38e074a`

````text
{
  "lean_invocations": 4,
  "cumulative_command_wall_seconds": 5.571168717986438,
  "cumulative_user_seconds": 4.090968,
  "cumulative_system_seconds": 2.2775969999999996,
  "cumulative_lock_wait_seconds": 5.357302143238485e-05,
  "max_peak_rss_kib": 3435348,
  "successful_invocation": 4,
  "exact_assignment_timestamp_recorded": false,
  "first_local_clock_observation_utc": "2026-11-24T00:12:41Z",
  "success_utc": "2026-11-24T00:14:17.746811+00:00"
}
````
