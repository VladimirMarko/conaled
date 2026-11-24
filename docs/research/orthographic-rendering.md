# Checked orthographic image sequence

[#690](https://github.com/VladimirMarko/conaled/issues/690) supplies the first
visible Euclidean 3D execution slice under [simulator #34](https://github.com/VladimirMarko/conaled/issues/34).
The exact rational scene, finite observations and output presentation are separate:

- [Orthographic](../../Applications/Rendering/Orthographic.lean) defines the world,
  positive-z rays, intersections, camera queries and response evaluation.
- [PPM](../../Applications/Rendering/PPM.lean) clamps and quantizes channels and
  serializes the resulting arrays to ASCII P3.
- [Checked clients](../../Examples/OrthographicRendering.lean) retain independent
  geometric, color, camera, saturation and serialization controls.
- [The IO driver](../../scripts/render-orthographic.lean) writes three files to a
  caller-selected directory. [The output test](../../scripts/test-orthographic-rendering.py)
  checks the real files and an asymmetric serializer fixture.

The shared [Response](../../Applications/Rendering/Response.lean) algebra still
has no coordinates or fixed dimension. Its new `eval_prod` theorem derives
finite front-to-back layering from `eval_mul` by induction. This is the law used
by the rendering computation, including layers that miss and contribute identity.

## World and observation

World points are rational triples. The near rectangle is at z=1, with closed
bounds x in [-1/2,1/2] and y in [-1,1], emission (1/2,0,0) and transmission 1/2.
The far rectangle is at z=2, with closed bounds x and y in [-1,1], emission
(0,1/2,0) and transmission zero. Incoming light is black.

Each camera is at z=0 and looks along (0,0,1). Camera x offsets are -1/2, 0 and
1/2. For column i and row j in {0,...,31}, the ray origin is
`(offset + (2*i+1)/16 - 2, 2 - (2*j+1)/16, 0)`.
These are exact point samples; neither pixel footprints nor antialiasing are modeled.

`hits_iff_intersection` identifies the executable hit predicate with existence of
a nonnegative ray parameter at the rectangle plane and inside its closed bounds.
`fixed_order` proves that the selected near intersection parameter is nonnegative
and strictly smaller than the far parameter for every camera and pixel. This
justifies the chosen order only for the supported parallel rays and two depths.
The ray type deliberately does not represent arbitrary directions.

`near_implies_far` proves containment for every supported ray, so no near-only
pixel exists. `renderRay_eq` uses `Response.eval_prod` to derive the three possible
colors: overlap (1/2,1/4,0), far-only (0,1/2,0), and black. `pixel_eq_spec` connects
the actual response computation to an independent region/color specification.
`scene_admissible` establishes nonnegative RGB emission and scalar transmission
in [0,1]. `pixel_bounds` additionally puts every observed channel in [0,1];
admissible emission alone does not imply that upper bound for arbitrary scenes.

`frame_get` connects the generated arrays to that specification, with the outer
index the row and inner index the column. `grid_corners` and `rows_descend` check
top-to-bottom world-y order. `encodedFrame_get` preserves those indices through
channel encoding. The runtime test compares every pixel against independently
worked integer bands. Because these scene images are vertically symmetric, an
additional asymmetric 2 by 2 fixture tests row, column and RGB serialization order.

## Quantization and execution boundary

A channel x is clamped to `max 0 (min 1 x)` and encoded as `floor(255*clamp x)`.
Decoding means integer/255. The encoded integer lies in [0,255], and the decoded
value is below the clamped channel by less than 1/255. The absolute error is
therefore at most 1/255. Inputs at or below zero encode as zero; inputs at or
above one encode as 255. The bound is relative to the clamped value, not to an
arbitrary out-of-range input. The checked input 2 separates those claims.
`scene_error` specializes the bound to the original scene channels because their
bounds have been proved. No floating-point approximation enters scene evaluation.

The pure serializer writes `P3`, dimensions `32 32`, maximum `255`, then RGB
integers in row-major order, one pixel per line. The overlap serializes as
`127 63 0`; far-only as `0 127 0`. Pure checked string fixtures and numerical
decoding facts do not prove filesystem writes or an external PPM viewer correct.
The executable tests check the actual ASCII bytes, parsed dimensions, channel
count/range, all expected pixels, deterministic replacement and differing frames.
Lean code generation, runtime arithmetic, OS writes/reads and the viewer remain
external execution assumptions. There is no formal general PPM parser round-trip
theorem or crash-atomic multi-file output contract.

## Reproduce and inspect

From a clean checkout at the source revision to record:

```sh
git rev-parse HEAD
direnv exec . lake build Examples.OrthographicRendering
direnv exec . lake env lean --run scripts/render-orthographic.lean /tmp/conaled-orthographic
direnv exec . python3 scripts/test-orthographic-rendering.py
sha256sum /tmp/conaled-orthographic/frame-*.ppm
```

The output is `frame-000.ppm`, `frame-001.ppm`, `frame-002.ppm`. Open them in a
PPM-capable viewer, preferably enlarged with nearest-neighbor scaling. Retain the
printed source revision, command and hashes with an artifact record when sharing
an output. Generated images and build products are not repository source files.
Exact-candidate acceptance additionally runs the integrated build and exhaustive
audit through `scripts/check-candidate.py` in its isolated workspace.

The expected artifact has 128 overlap pixels, 128 far-only pixels and 768 black
pixels in each frame. Colored rows are 8 through 23 inclusive. Far columns are
12..27, 8..23 and 4..19 respectively; overlap columns are 16..23, 12..19 and 8..15.
The red/green overlap band and exposed green bands move four columns left per
frame as the camera moves right. There is no blue contribution. Separate exact
boundary controls matter because these pixel centers do not land on the edges.

## Remaining scope

This experiment supports bounded parallel rectangles, a fixed orthographic
camera family and emission/transmission layering. It produces a visible camera
sequence without adopting a universal renderer interface. There is no mesh,
perspective, arbitrary sorting, scattering, interreflection, stochastic sampling,
GPU backend, interactive runtime or certified cache substitution here. A genuinely
3D orbifold world still needs its geometric presentation, representative/frame
transport, isotropy-sensitive observation and motion contracts under #34.
