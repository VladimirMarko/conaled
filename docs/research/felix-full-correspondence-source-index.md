# Pinned Felix declaration and proposal index

Companion to [the correspondence assessment](felix-full-correspondence.md).

This index covers every `.agda` file under `src/Felix` at the pinned revision.
Each module links to its complete source, retaining signatures, module parameters,
proof bodies, local helper definitions and commented alternatives. The declaration
locators below include record fields and private helpers conservatively; presence
in this index does not assert that a private helper is a public API. Re-exported
declarations are owned by their defining module. Module dispositions and residual
contracts are in the companion assessment. Counts describe source indexing, not
completed Lean ports.

## All.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/All.agda), 26 lines, SHA-256 `9a8fba11b6caece496dd4d5fa45bdb39f143468fe35fcb796eff7b74b88686c8`.

| Declaration / source locator |
|---|
| Re-export module; see complete imports above. |

## Construct/Arrow.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda), 90 lines, SHA-256 `964f9f51f05c6e41e287534a6ea8eadadd2a5b3aa14fe6c1dc3108d817044c7d`.

| Declaration / source locator |
|---|
| [`Hₒ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L20) |
| [`H`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L23) |
| [`catH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L26) |
| [`productsH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L40) |
| [`strongProductsH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L43) |
| [`cartesianH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L46) |
| [`_ᵀ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L57) |
| [`composableᵒ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L63) |
| [`_○_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L67) |
| [`vcomposable`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L72) |
| [`_◎_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L78) |
| [`Id`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L85) |
| [`idᵀ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L88) |

Inactive signatures, unfinished proposals and maintenance notes (including abandoned alternatives):

- [Line 29](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L29): `TODO: Replace Hₒ, H, etc by a bundle`
- [Line 49](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L49): `booleanH : BooleanH obj _↠_`
- [Line 52](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L52): `strongBooleanH : StrongBooleanH obj _↠_`
- [Line 75](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L75): `vcomposable ⦃ p@refl ⦄ ⦃ q@refl ⦄ (mkᵐ _ fₕ₂ _) (mkᵐ fₖ₁ _ _) = {!!}`
- [Line 83](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Arrow.agda#L83): `TODO: Generalize vertical composition to general comma categories.`

## Construct/Comma/Homomorphism.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Homomorphism.agda), 40 lines, SHA-256 `c9f09c808cbb3bbfd90f4767cf29b98a332810cda2be2a79dfa099031699a24f`.

| Declaration / source locator |
|---|
| [`categoryH₁`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Homomorphism.agda#L32) |
| [`categoryH₂`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Homomorphism.agda#L36) |

## Construct/Comma/Raw.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda), 352 lines, SHA-256 `38a618c4e2b6ea2138971c6b41e31e4f3c872032f80fe47823b2954f747f0c1c`.

| Declaration / source locator |
|---|
| [`id′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L47) |
| [`comp`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L66) |
| [`category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L73) |
| [`products`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L87) |
| [`!′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L107) |
| [`fork`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L124) |
| [`exl′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L146) |
| [`exr′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L166) |
| [`cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L175) |

Inactive signatures, unfinished proposals and maintenance notes (including abandoned alternatives):

- [Line 36](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L36): `id′ : a ↬ a`
- [Line 50](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L50): `comp : (b ↬ c) → (a ↬ b) → (a ↬ c)`
- [Line 92](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L92): `!′ : a ↬ ⊤`
- [Line 110](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L110): `fork : (a ↬ c) → (a ↬ d) → (a ↬ c × d)`
- [Line 133](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L133): `exl′ : a × b ↬ a`
- [Line 153](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L153): `exr′ : a × b ↬ b`
- [Line 186](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L186): `-- TODO: remove cartesian stuff as able`
- [Line 197](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L197): `boolean : Boolean Obj`
- [Line 200](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L200): `-- false′ : ⊤ ↬ Bool`
- [Line 221](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L221): `false′ : ⊤ ↬ Bool`
- [Line 228](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L228): `true′ : ⊤ ↬ Bool`
- [Line 248](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L248): `not′ : Bool ↬ Bool`
- [Line 255](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L255): `-- ∧′ : Bool × Bool ↬ Bool`
- [Line 277](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L277): `∧′ : Bool × Bool ↬ Bool`
- [Line 286](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L286): `∨′ : Bool × Bool ↬ Bool`
- [Line 295](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L295): `xor′ : Bool × Bool ↬ Bool`
- [Line 304](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L304): `-- cond′ : Bool × (a × a) ↬ a`
- [Line 332](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L332): `cond′ : Bool × (a × a) ↬ a`
- [Line 344](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Raw.agda#L344): `logic : Logic _↬_`

## Construct/Comma/Type.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda), 77 lines, SHA-256 `7f50de97661642dcdf0b100352f57d65f1e480d29bb8fbc8fca15fd9bdebe095`.

| Declaration / source locator |
|---|
| [`Obj`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L24) |
| [`constructor mkᵒ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L25) |
| [`{ τ₁ }`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L27) |
| [`{ τ₂ }`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L28) |
| [`h`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L29) |
| [`_↬_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L34) |
| [`constructor mkᵐ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L35) |
| [`f₁`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L37) |
| [`f₂`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L38) |
| [`↻`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L39) |
| [`_⇉_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L45) |
| [`Hₒ×`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L56) |
| [`H×`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L59) |
| [`equivalent`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L62) |
| [`Hₒ₁`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L66) |
| [`H₁`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L69) |
| [`Hₒ₂`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L73) |
| [`H₂`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L76) |

Inactive signatures, unfinished proposals and maintenance notes (including abandoned alternatives):

- [Line 22](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda#L22): `TODO: Define some bundles to reduce syntactic clutter.`

## Construct/Comma/Vertical.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Vertical.agda), 62 lines, SHA-256 `cfe998d52088cfc3779476346d3c8aed95048f449d938f6bfee6c02f79d4d96b`.

| Declaration / source locator |
|---|
| [`_◎_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Vertical.agda#L41) |

## Construct/Comma.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma.agda), 25 lines, SHA-256 `ff547f6b241409695a22beb33645bbd4150b7fdc0eb7fe584beb29180bb97896`.

| Declaration / source locator |
|---|
| Re-export module; see complete imports above. |

## Construct/Monoid.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Monoid.agda), 40 lines, SHA-256 `0a6502a3fb35f0bf53ac1ccbb48ff3729eeea2e7bd8ae97d97faa305c0b2c415`.

| Declaration / source locator |
|---|
| [`_⇒_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Monoid.agda#L15) |
| [`constructor mk⇒`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Monoid.agda#L16) |
| [`category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Monoid.agda#L26) |
| [`equivalent`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Monoid.agda#L31) |
| [`lawful-category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Monoid.agda#L34) |

## Construct/Product.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda), 251 lines, SHA-256 `ad64d3576147f0886eb4377897e36b5db4403d34289674e65ab61477465b388c`.

| Declaration / source locator |
|---|
| [`Obj`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L18) |
| [`_⇨_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L22) |
| [`category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L27) |
| [`products`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L30) |
| [`cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L33) |
| [`traced`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L43) |
| [`equivalent`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L69) |
| [`l-category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L81) |
| [`l-cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L93) |
| [`Hₒ₁`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L132) |
| [`H₁`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L135) |
| [`Hₒ₂`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L138) |
| [`H₂`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L141) |
| [`catH₁`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L144) |
| [`catH₂`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L148) |
| [`pH₁`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L152) |
| [`spH₁`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L155) |
| [`pH₂`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L164) |
| [`spH₂`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L167) |
| [`cartesianH₁`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L176) |
| [`cartesianH₂`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L187) |

Inactive signatures, unfinished proposals and maintenance notes (including abandoned alternatives):

- [Line 52](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L52): `boolean : ⦃ _ : Boolean obj₁ ⦄ ⦃ _ : Boolean obj₂ ⦄ → Boolean Obj`
- [Line 55](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L55): `logic : ⦃ _ : Products obj₁ ⦄ ⦃ _ : Products obj₂ ⦄`
- [Line 121](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L121): `l-logic : ∀ {q₁} ⦃ _ : Equivalent q₁ _⇨₁_ ⦄ {q₂} ⦃ _ : Equivalent q₂ _⇨₂_ ⦄`
- [Line 198](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L198): `booleanH₁ :`
- [Line 204](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L204): `booleanH₂ :`
- [Line 210](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L210): `strongBooleanH₁ :`
- [Line 218](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L218): `logicH₁ : ∀ {q₁} ⦃ _ : Equivalent q₁ _⇨₁_ ⦄`
- [Line 235](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L235): `logicH₂ : ∀ {q₂} ⦃ _ : Equivalent q₂ _⇨₂_ ⦄`
- [Line 251](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Product.agda#L251): `-- TODO: Factor out some of the instance requirements as submodule arguments.`

## Construct/Squared.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Squared.agda), 68 lines, SHA-256 `8b3089fb282e30863476803eb80f3234ea19e4e116c533f80caf4adea261583f`.

| Declaration / source locator |
|---|
| [`unsquare`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Squared.agda#L23) |
| [`Hₒ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Squared.agda#L32) |
| [`H`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Squared.agda#L36) |
| [`catH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Squared.agda#L40) |
| [`pH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Squared.agda#L43) |
| [`spH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Squared.agda#L46) |
| [`cartH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Squared.agda#L52) |
| [`equivalent`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Squared.agda#L61) |
| [`catL`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Squared.agda#L67) |

## Equiv.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Equiv.agda), 118 lines, SHA-256 `9274dc0990216e3bc697033c2bb2d812d61c1e48169628b40ead2218c08dac96`.

| Declaration / source locator |
|---|
| [`obj`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Equiv.agda#L14) |
| [`Equivalent`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Equiv.agda#L17) |
| [`_≈_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Equiv.agda#L21) |
| [`equiv`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Equiv.agda#L22) |
| [`≈setoid`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Equiv.agda#L29) |
| [`refl≈`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Equiv.agda#L35) |
| [`sym≈`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Equiv.agda#L38) |
| [`_•_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Equiv.agda#L42) |
| [`_;_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Equiv.agda#L46) |
| [`Homomorphismₒ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Equiv.agda#L52) |
| [`Fₒ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Equiv.agda#L54) |
| [`id-Hₒ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Equiv.agda#L58) |
| [`_∘Hₒ_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Equiv.agda#L62) |
| [`_▵Hₒ_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Equiv.agda#L68) |
| [`Homomorphism`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Equiv.agda#L74) |
| [`Fₘ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Equiv.agda#L80) |
| [`id-H`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Equiv.agda#L84) |
| [`_∘H_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Equiv.agda#L88) |
| [`_▵H_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Equiv.agda#L98) |
| [`H-equiv`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Equiv.agda#L112) |

Inactive signatures, unfinished proposals and maintenance notes (including abandoned alternatives):

- [Line 51](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Equiv.agda#L51): `TODO: consider moving to Felix.Homomorphism.`

## Homomorphism.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda), 490 lines, SHA-256 `1d8274af6d623c76e10c0c172df9d70b29590f1c6cd3b5a987ccdd3417e0ca3c`.

| Declaration / source locator |
|---|
| [`CategoryH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L21) |
| [`F-cong`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L29) |
| [`F-id`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L30) |
| [`F-∘`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L31) |
| [`F-∘³`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L37) |
| [`F-∘⁴`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L42) |
| [`F-∘⁵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L47) |
| [`F-∘⁶`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L53) |
| [`id-CategoryH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L62) |
| [`_∘-CategoryH_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L70) |
| [`compose-CategoryH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L92) |
| [`ProductsH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L129) |
| [`ε`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L138) |
| [`μ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L139) |
| [`ε⁻¹`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L141) |
| [`μ⁻¹`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L142) |
| [`id-ProductsH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L146) |
| [`compose-ProductsH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L152) |
| [`StrongProductsH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L168) |
| [`ε⁻¹∘ε`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L179) |
| [`ε∘ε⁻¹`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L180) |
| [`μ⁻¹∘μ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L182) |
| [`μ∘μ⁻¹`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L183) |
| [`id-StrongProductsH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L187) |
| [`CartesianH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L203) |
| [`F-!`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L214) |
| [`F-▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L215) |
| [`F-exl`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L216) |
| [`F-exr`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L217) |
| [`F-!′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L222) |
| [`F-▵′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L225) |
| [`F-exl′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L228) |
| [`F-exr′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L231) |
| [`F-⊗`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L236) |
| [`F-⊗′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L250) |
| [`F-first`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L262) |
| [`F-first′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L266) |
| [`F-second`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L270) |
| [`F-second′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L274) |
| [`F-assocˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L278) |
| [`F-assocˡ′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L301) |
| [`F-assocʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L312) |
| [`F-assocʳ′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L347) |
| [`id-CartesianH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L360) |
| [`_∘-CartesianH_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L374) |
| [`CoproductsH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L435) |
| [`δ⁻¹`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L443) |
| [`ν⁻¹`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L444) |
| [`δ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L446) |
| [`ν`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L447) |
| [`id-CoproductsH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L451) |
| [`CocartesianH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L458) |
| [`F-¡`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L469) |
| [`F-▿`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L470) |
| [`F-inl`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L471) |
| [`F-inr`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L472) |
| [`ExponentialsH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L477) |
| [`ζ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L484) |
| [`ζ⁻¹`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L486) |

Inactive signatures, unfinished proposals and maintenance notes (including abandoned alternatives):

- [Line 32](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L32): `TODO: make g and f explicit arguments? Wait and see.`
- [Line 90](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L90): `TODO: Phase out _∘-CategoryH_ in favor of`
- [Line 109](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L109): `_▵-CategoryH_ :`
- [Line 137](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L137): `https://ncatlab.org/nlab/show/monoidal+functor`
- [Line 197](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L197): `TODO: Try defining id-ProductsH via id-ProductsH′.`
- [Line 199](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L199): `TODO: Try defining an instance module in place of id-ProductsH′ and`
- [Line 490](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L490): `TODO: CartesianClosedH`

## Instances/CAT.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/CAT.agda), 115 lines, SHA-256 `4753beffddbaa60d6543b7b08b084dad6f5cbeb7fe2610a2ec69b99ca8949c77`.

| Declaration / source locator |
|---|
| [`CAT`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/CAT.agda#L19) |
| [`constructor cat`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/CAT.agda#L20) |
| [`{obj}`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/CAT.agda#L22) |
| [`mor`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/CAT.agda#L23) |
| [`_⤇_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/CAT.agda#L26) |
| [`constructor mk⤇`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/CAT.agda#L27) |
| [`Fₒ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/CAT.agda#L31) |
| [`Fₘ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/CAT.agda#L32) |
| [`category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/CAT.agda#L36) |
| [`products`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/CAT.agda#L42) |
| [`cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/CAT.agda#L49) |
| [`toHₒ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/CAT.agda#L67) |
| [`toH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/CAT.agda#L70) |
| [`it-⤇`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/CAT.agda#L73) |
| [`Functor`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/CAT.agda#L96) |
| [`catH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/CAT.agda#L98) |
| [`CartesianFunctor`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/CAT.agda#L104) |
| [`cartH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/CAT.agda#L107) |

Inactive signatures, unfinished proposals and maintenance notes (including abandoned alternatives):

- [Line 81](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/CAT.agda#L81): `Experiment: functor classes`
- [Line 109](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/CAT.agda#L109): `Next: (cartesian) functors compose`
- [Line 114](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/CAT.agda#L114): `category : Category Functor`

## Instances/Function/Laws.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Laws.agda), 76 lines, SHA-256 `bfcb2696270bea012efab9061afcc92d1470fe9183e0c39eeb332c4cd990ba80`.

| Declaration / source locator |
|---|
| [`category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Laws.agda#L27) |
| [`cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Laws.agda#L36) |
| [`cocartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Laws.agda#L45) |
| [`distributive`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Laws.agda#L52) |
| [`cartesianClosed`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Laws.agda#L70) |

## Instances/Function/Lift.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Lift.agda), 71 lines, SHA-256 `e7cd6984a0ff4d07736e9cd682eaed32395c2c3f31079b553b6fb2c9e0ece4d4`.

| Declaration / source locator |
|---|
| [`A`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Lift.agda#L18) |
| [`lift₀′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Lift.agda#L20) |
| [`lift₀`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Lift.agda#L23) |
| [`lift₁`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Lift.agda#L26) |
| [`lift₂′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Lift.agda#L29) |
| [`lift₂`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Lift.agda#L32) |
| [`Hₒ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Lift.agda#L37) |
| [`H`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Lift.agda#L40) |
| [`catH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Lift.agda#L45) |
| [`pH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Lift.agda#L52) |
| [`spH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Lift.agda#L59) |
| [`cartH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Lift.agda#L66) |

## Instances/Function/Raw.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Raw.agda), 55 lines, SHA-256 `4bcbc1e2b9188f94c1cf93f7e834e178666935a58612a448559dadf8085da0f0`.

| Declaration / source locator |
|---|
| [`category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Raw.agda#L18) |
| [`cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Raw.agda#L21) |
| [`cocartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Raw.agda#L24) |
| [`distributive`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Raw.agda#L27) |
| [`traced`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Raw.agda#L33) |
| [`cartesianClosed`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Raw.agda#L39) |
| [`equivalent`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Raw.agda#L45) |

Inactive signatures, unfinished proposals and maintenance notes (including abandoned alternatives):

- [Line 44](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Raw.agda#L44): `TODO: move to Relation.Binary.PropositionalEquality.Properties as a PR`

## Instances/Function/Type.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Type.agda), 32 lines, SHA-256 `991d30f9f28189c3dd3b069b3d0e5e3ec4113fe5683426c5669dc030673ce16e`.

| Declaration / source locator |
|---|
| [`_⇾_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Type.agda#L14) |
| [`pattern tt`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Type.agda#L17) |
| [`products`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Type.agda#L25) |
| [`coproducts`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Type.agda#L28) |
| [`exponentials`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Type.agda#L31) |

## Instances/Function.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function.agda), 6 lines, SHA-256 `0ec599ecc61db05c66839d3c62de5220cbf7515c4f665800550d657caed768db`.

| Declaration / source locator |
|---|
| Re-export module; see complete imports above. |

## Instances/Identity.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Identity.agda), 54 lines, SHA-256 `609ec96cfb8586fd0a74ebea9db5a81f10b279a80bc235957263ae681b021cab`.

| Declaration / source locator |
|---|
| [`Hₒ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Identity.agda#L18) |
| [`H`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Identity.agda#L21) |
| [`pH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Identity.agda#L24) |
| [`catH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Identity.agda#L36) |
| [`spH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Identity.agda#L39) |
| [`cartH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Identity.agda#L42) |

Inactive signatures, unfinished proposals and maintenance notes (including abandoned alternatives):

- [Line 28](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Identity.agda#L28): `bH : ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄ ⦃ _ : Category _⇨_ ⦄`
- [Line 46](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Identity.agda#L46): `sbH : ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄ ⦃ _ : L.Category _⇨_ ⦄`
- [Line 50](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Identity.agda#L50): `lH : ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄`

## Instances/Pred.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda), 137 lines, SHA-256 `58a28921845b842c72e34c8c567de8601942812f2b02b166962a506119fd6ad1`.

| Declaration / source locator |
|---|
| [`PRED`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L24) |
| [`constructor mkᵒ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L25) |
| [`{ty}`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L27) |
| [`pred`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L28) |
| [`products`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L32) |
| [`coproducts`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L35) |
| [`_⇒_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L42) |
| [`constructor mkᵐ `](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L43) |
| [`{f}`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L45) |
| [`imp`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L46) |
| [`rawCategory`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L53) |
| [`rawCartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L59) |
| [`rawCocartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L67) |
| [`equivalent`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L81) |
| [`Hₒ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L96) |
| [`H`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L99) |
| [`catH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L102) |
| [`pH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L109) |
| [`spH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L114) |
| [`cartH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L118) |
| [`category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L133) |
| [`cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L136) |

Inactive signatures, unfinished proposals and maintenance notes (including abandoned alternatives):

- [Line 77](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L77): `Equiv: on the underlying function`
- [Line 90](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Pred.agda#L90): `Homomorphisms: Project away the predicates and proofs`

## Instances/Setoids.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda), 219 lines, SHA-256 `d2a0c096f607a6c72535cf429cfa22e385b6cb73e03e12623a4ee83135060648`.

| Declaration / source locator |
|---|
| [`Zoid`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L39) |
| [`_⟶_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L42) |
| [`A`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L47) |
| [`pattern tt`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L49) |
| [`pattern _⊨_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L52) |
| [`𝟘`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L59) |
| [`𝟙`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L69) |
| [`absurd`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L74) |
| [`products`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L82) |
| [`coproducts`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L85) |
| [`exponentials`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L88) |
| [`rawCategory`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L96) |
| [`rawCartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L102) |
| [`rawCocartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L110) |
| [`rawCartesianClosed`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L118) |
| [`rawDistributive`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L127) |
| [`equivalent`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L153) |
| [`category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L166) |
| [`cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L175) |
| [`cocartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L184) |
| [`cartesianClosed`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L193) |
| [`distributive`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L201) |

Inactive signatures, unfinished proposals and maintenance notes (including abandoned alternatives):

- [Line 137](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L137): `TODO?`
- [Line 138](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L138): `rawTraced : Raw.Traced _⟶_`
- [Line 143](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L143): `→ {!   !} -- _≈_ (B * S) (to f (x , z)) (y , z)`
- [Line 145](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L145): `; trace = λ {A} {S} {B} f g → (×.proj₁ ∘ g) ⊨ λ { {x} {y} x≈y → {!   !} }`
- [Line 217](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L217): `Needs laws`
- [Line 218](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Setoids.agda#L218): `traced : Traced _⟶ₛ_`

## Laws.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda), 344 lines, SHA-256 `266b128c0ff0b45e0e0b76e42210ab997af79cbc02cf83212b10a29be921ee0c`.

| Declaration / source locator |
|---|
| [`obj`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L19) |
| [`Category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L23) |
| [`identityˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L29) |
| [`identityʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L30) |
| [`assoc`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L31) |
| [`∘≈`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L34) |
| [`∘-assocʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L37) |
| [`∘-assocˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L40) |
| [`∘≈ˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L43) |
| [`∘≈ʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L46) |
| [`Cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L54) |
| [`∀⊤`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L62) |
| [`∀×`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L64) |
| [`▵≈`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L68) |
| [`∀×→`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L70) |
| [`∀×←`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L74) |
| [`▵≈ˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L78) |
| [`▵≈ʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L81) |
| [`exl∘▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L88) |
| [`exr∘▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L91) |
| [`exl∘⊗`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L95) |
| [`exr∘⊗`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L97) |
| [`exl∘first`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L100) |
| [`exr∘first`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L103) |
| [`exl∘second`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L106) |
| [`exr∘second`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L109) |
| [`exl▵exr`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L112) |
| [`⊗≈`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L115) |
| [`⊗≈ˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L130) |
| [`⊗≈ʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L134) |
| [`id⊗id`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L138) |
| [`▵∘`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L141) |
| [`⊗∘▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L144) |
| [`first∘▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L159) |
| [`second∘▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L163) |
| [`⊗∘⊗`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L167) |
| [`first∘⊗`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L171) |
| [`⊗∘first`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L176) |
| [`⊗∘second`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L180) |
| [`second∘⊗`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L184) |
| [`first∘first`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L188) |
| [`second∘second`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L192) |
| [`first∘second`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L196) |
| [`second∘first`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L200) |
| [`unitorᵉˡ∘unitorⁱˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L207) |
| [`unitorᵉʳ∘unitorⁱʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L210) |
| [`unitorⁱˡ∘unitorᵉˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L213) |
| [`unitorⁱʳ∘unitorᵉʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L222) |
| [`exl∘swap`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L234) |
| [`exr∘swap`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L237) |
| [`swap∘▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L240) |
| [`swap∘swap`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L256) |
| [`Cocartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L275) |
| [`∀⊥`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L283) |
| [`∀⊎`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L285) |
| [`▿≈`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L288) |
| [`Distributive`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L292) |
| [`distribˡ∘distribˡ⁻¹`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L301) |
| [`distribˡ⁻¹∘distribˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L302) |
| [`distribʳ∘distribʳ⁻¹`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L303) |
| [`distribʳ⁻¹∘distribʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L304) |
| [`CartesianClosed`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L309) |
| [`∀⇛`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L319) |
| [`curry≈`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L323) |
| [`∀⇛→`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L325) |
| [`∀⇛←`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L329) |
| [`curry-apply`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L333) |

Inactive signatures, unfinished proposals and maintenance notes (including abandoned alternatives):

- [Line 33](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L33): `TODO: infix?`
- [Line 36](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L36): `TODO: replace the assoc field after I've inspected all uses`
- [Line 67](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L67): `TODO: infix?`
- [Line 85](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L85): `TODO: Generalize Function category from level 0, and use exl & exr in place`
- [Line 94](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L94): `Specializing:`
- [Line 204](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L204): `TODO: redefine first f and second g via ▵ to avoid id ∘ exr and id ∘ exl.`
- [Line 231](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L231): `swap : a × b ⇨ b × a`
- [Line 254](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L254): `TODO: Revisit swap∘swap given swap∘▵`
- [Line 320](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L320): `Note: uncurry g ≡ apply ∘ first g ≡ apply ∘ (g ⊗ id)`

## MakeLawful.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/MakeLawful.agda), 149 lines, SHA-256 `20acf061e726577462bb3bd2fd65c5a52f71ef22d1de0b0de5f35e5e7929989f`.

| Declaration / source locator |
|---|
| [`LawfulCategoryᶠ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/MakeLawful.agda#L33) |
| [`LawfulCartesianᶠ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/MakeLawful.agda#L87) |

Inactive signatures, unfinished proposals and maintenance notes (including abandoned alternatives):

- [Line 148](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/MakeLawful.agda#L148): `TODO: CartesianClosed, etc.`

## Object.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Object.agda), 26 lines, SHA-256 `996d6e0a37168cd22d074c66c7a007fdbbfc8db2264bffd1574551aec72ab63c`.

| Declaration / source locator |
|---|
| [`Products`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Object.agda#L8) |
| [`⊤`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Object.agda#L11) |
| [`_×_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Object.agda#L12) |
| [`Coproducts`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Object.agda#L15) |
| [`⊥`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Object.agda#L18) |
| [`_⊎_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Object.agda#L19) |
| [`Exponentials`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Object.agda#L22) |
| [`_⇛_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Object.agda#L25) |

## Prop.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Prop.agda), 41 lines, SHA-256 `38f04412ec83f52f637511f84a8dc97930292e5d7b200491933fd010310e9f90`.

| Declaration / source locator |
|---|
| [`Categoryᴾ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Prop.agda#L14) |
| [`idᴾ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Prop.agda#L17) |
| [`_∘ᴾ_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Prop.agda#L18) |
| [`Cartesianᴾ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Prop.agda#L21) |
| [`!ᴾ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Prop.agda#L25) |
| [`_▵ᴾ_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Prop.agda#L26) |
| [`exlᴾ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Prop.agda#L27) |
| [`exrᴾ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Prop.agda#L28) |

Inactive signatures, unfinished proposals and maintenance notes (including abandoned alternatives):

- [Line 31](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Prop.agda#L31): `record Logicᴾ ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄ ⦃ _ : Logic _↠_ ⦄`
- [Line 34](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Prop.agda#L34): `falseᴾ : M false`
- [Line 35](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Prop.agda#L35): `trueᴾ  : M true`
- [Line 36](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Prop.agda#L36): `notᴾ   : M not`
- [Line 37](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Prop.agda#L37): `∧ᴾ     : M ∧`
- [Line 38](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Prop.agda#L38): `∨ᴾ     : M ∨`
- [Line 39](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Prop.agda#L39): `xorᴾ   : M xor`
- [Line 40](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Prop.agda#L40): `condᴾ  : M (cond {a = a})`

## Raw.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda), 187 lines, SHA-256 `eb02e4f912d35d1d59548570b360db2a95e395641c90dc0e443cb2c6068dac24`.

| Declaration / source locator |
|---|
| [`Category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L17) |
| [`id`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L20) |
| [`_∘_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L21) |
| [`sub`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L25) |
| [`sub≡`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L28) |
| [`Cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L34) |
| [`!`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L41) |
| [`_▵_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L42) |
| [`exl`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L43) |
| [`exr`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L44) |
| [`dup`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L46) |
| [`_⊗_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L52) |
| [`first`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L55) |
| [`second`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L58) |
| [`twice`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L61) |
| [`unitorᵉˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L64) |
| [`unitorᵉʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L67) |
| [`unitorⁱˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L70) |
| [`unitorⁱʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L73) |
| [`constˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L76) |
| [`constʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L79) |
| [`assocˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L82) |
| [`assocʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L85) |
| [`inAssocˡ′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L88) |
| [`inAssocˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L91) |
| [`inAssocʳ′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L94) |
| [`inAssocʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L97) |
| [`swap`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L100) |
| [`inSwap`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L103) |
| [`transpose`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L106) |
| [`inTranspose`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L109) |
| [`_⦂_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L114) |
| [`Cocartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L120) |
| [`¡`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L127) |
| [`_▿_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L128) |
| [`inl`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L129) |
| [`inr`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L130) |
| [`jam`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L132) |
| [`Distributive`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L140) |
| [`distribˡ⁻¹`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L148) |
| [`distribʳ⁻¹`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L149) |
| [`distribˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L151) |
| [`distribʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L154) |
| [`Traced`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L160) |
| [`WF`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L166) |
| [`trace`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L167) |
| [`CartesianClosed`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L172) |
| [`curry`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L181) |
| [`apply`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L182) |
| [`uncurry`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L184) |

Inactive signatures, unfinished proposals and maintenance notes (including abandoned alternatives):

- [Line 137](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L137): `TODO: Factor a bunch of functionality out of Cartesian and some out of Cocartesian in Monoidal.`

## Reasoning.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda), 569 lines, SHA-256 `f7e4fb0b72f2eae008d9d539216fc028c4b158f2034340e7cfe349f8af00b5a8`.

| Declaration / source locator |
|---|
| [`sym≈-sym≈`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L31) |
| [`elimˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L42) |
| [`introˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L51) |
| [`elimʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L54) |
| [`introʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L63) |
| [`elim-center`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L66) |
| [`intro-center`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L69) |
| [`∘-assocˡ′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L79) |
| [`∘-assocʳ′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L83) |
| [`∘-assocˡʳ′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L88) |
| [`∘-assocʳˡ′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L92) |
| [`∘-assoc-elimˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L97) |
| [`∘-assoc-elimʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L101) |
| [`∘-assocʳ³`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L106) |
| [`∘-assocʳ⁴`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L111) |
| [`∘-assocʳ⁵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L116) |
| [`∘-assocʳ⁶`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L121) |
| [`∘-assocˡ³`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L126) |
| [`∘-assocˡ⁴`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L131) |
| [`∘-assocˡ⁵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L136) |
| [`∘-assocˡ⁶`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L142) |
| [`∘≈ʳ²`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L148) |
| [`∘≈ʳ³`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L152) |
| [`∘≈ʳ⁴`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L157) |
| [`∘≈ʳ⁵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L162) |
| [`∘≈ʳ⁶`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L168) |
| [`cancelʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L180) |
| [`cancelˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L193) |
| [`cancelInner`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L206) |
| [`∘-inverse`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L220) |
| [`⊗-inverse`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L224) |
| [`first-inverse`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L229) |
| [`second-inverse`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L233) |
| [`assocˡ∘assocʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L243) |
| [`assocʳ∘assocˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L267) |
| [`assocʳ∘▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L288) |
| [`assocˡ∘▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L303) |
| [`⊗⊗∘assocʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L320) |
| [`⊗⊗∘assocˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L349) |
| [`first-first∘assocˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L376) |
| [`first-first`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L393) |
| [`inAssocˡ′-inverse`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L404) |
| [`inAssocʳ′-inverse`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L420) |
| [`inAssocˡ-inverse`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L436) |
| [`inAssocʳ-inverse`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L447) |
| [`!⊗!`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L458) |
| [`[exl⊗exl]∘transpose`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L474) |
| [`[exr⊗exr]∘transpose`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L491) |
| [`transpose∘▵▵▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L508) |
| [`transpose∘▵⊗▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L536) |
| [`transpose∘transpose`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L552) |

Inactive signatures, unfinished proposals and maintenance notes (including abandoned alternatives):

- [Line 77](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L77): `TODO: Maybe move ∘-assocˡ′ and ∘-assocʳ′ to Pulls`
- [Line 190](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L190): `insertʳ : {f : b ⇨ d} → f ≈ (f ∘ h) ∘ i`
- [Line 203](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L203): `insertˡ : {f : a ⇨ b} →  f ≈ h ∘ (i ∘ f)`
- [Line 318](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Reasoning.agda#L318): `TODO: rework ⊗⊗∘assocʳ below, given assocʳ∘▵`

## Subcategory/Morphism.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda), 86 lines, SHA-256 `a36193feefa18e0e7ad5c609c053dfccf591d0a8cb72119d88c2c83218e6eedc`.

| Declaration / source locator |
|---|
| [`_⇨_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L23) |
| [`constructor mk`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L24) |
| [`f`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L26) |
| [`sat`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L27) |
| [`refl↠`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L30) |
| [`identityʳ↠`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L33) |
| [`sym-identityˡ↠`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L38) |
| [`H`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L47) |
| [`eq`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L50) |
| [`cat`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L53) |
| [`catH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L59) |
| [`l-category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L64) |
| [`cart`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L69) |
| [`cartH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L77) |
| [`l-cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Morphism.agda#L85) |

## Subcategory/Object.agda

[Complete pinned source](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda), 112 lines, SHA-256 `a995f732dc44b445e905618a62a087cce98af7560cbf27fdb4479dd70983f4d3`.

| Declaration / source locator |
|---|
| [`_⇨_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L28) |
| [`constructor mk`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L29) |
| [`un`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L31) |
| [`refl≈↠`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L35) |
| [`category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L40) |
| [`cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L43) |
| [`cocartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L52) |
| [`traced`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L61) |
| [`H`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L69) |
| [`equivalent`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L72) |
| [`categoryH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L75) |
| [`productsH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L78) |
| [`strongProductsH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L82) |
| [`cartesianH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L92) |
| [`l-category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L104) |
| [`l-cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L107) |

Inactive signatures, unfinished proposals and maintenance notes (including abandoned alternatives):

- [Line 80](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L80): `TODO: id-ProductsH?`
- [Line 90](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Subcategory/Object.agda#L90): `TODO: id-StrongProductsH?`

Indexed 29 modules and 471 declaration/field/helper locators.

Reproduction: enumerate `git ls-tree -r --name-only <pin> -- src/Felix`,
compare the module headings, verify each SHA-256 against the pinned blob, and
inspect signature/record/pattern starts plus the inferred `Zoid` alias. Comments
are not active declarations. No upstream Agda compilation is claimed here.
