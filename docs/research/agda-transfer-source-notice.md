# Source and license for the first transfer

The adapted proof is `tr-concat` in agda-unimath's
[foundation-core.transport-along-identifications](https://github.com/UniMath/agda-unimath/blob/75518656f287c203b41cb7f71df46e02b987a084/src/foundation-core/transport-along-identifications.lagda.md),
at revision `75518656f287c203b41cb7f71df46e02b987a084`.
The concatenation convention is taken from
[foundation-core.identity-types](https://github.com/UniMath/agda-unimath/blob/75518656f287c203b41cb7f71df46e02b987a084/src/foundation-core/identity-types.lagda.md)
at the same revision: the first path is eliminated, so `refl · q` computes to `q`.

The relevant proof dependencies are identity formation/reflexivity/elimination,
transport defined by identity elimination, and this first-path concatenation.
The external context parameters represent a base and its family; the fragment
does not add an internal universe or dependent function type to express the
upstream module parameters. The generalized `z`, `q`, and `b` remain in the
elimination motive. The branch is reflexivity after generated computation of
concat and transport.

The files were inspected at the pinned revision. No upstream Agda build or
rechecking claim is made. Lean checks concern the translated source derivations,
their interpretation, and the retained applications.

The upstream MIT notice is preserved below for the adapted definitions and
proof argument. The implementation's additional interpretation and authoring
machinery is documented separately in `first-transfer-design.md`.

MIT License

Copyright (c) 2022 Egbert Maarten Rijke

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
