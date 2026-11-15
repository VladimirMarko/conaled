# Direct toolchain scope and test seams

The user explicitly authorizes obtaining and using the required Lean and Lake
versions without Nix in `requirements/REQUEST-direct-toolchain-041.md`.
This continues the existing implementation loop and does not waive proof or
review requirements. Formal source branches are excluded from this tooling
change and retain their separate reviews.

The public seams under test are the Lean CLI, Lake's invocation of Lean, and
the stock project validation command. These are the existing project validation
interfaces requested by the user; no additional product interface or private
implementation test seam is introduced. Lean must accept a valid theorem and
reject a false theorem with a genuine type-checking diagnostic. Lake must
report its bundled exact version and build through the real compiler. The
full project check remains the authority for source policy, build, and axioms.
Compiler smoke tests alone cannot establish formal project acceptance.

The pre-change native probes are retained, including the missing shared-library
search path and absent process executable metadata failures. The first test
run uses the original distribution, scoped library search paths, and no
launcher profile. Subsequent runs use the same public interfaces through the
workspace-local launcher. Original release binaries remain unchanged.

The implementation consists of reproducible profile/launcher source, public
interface smoke tests, and recorded validation runners in `session/`. Binary
downloads, extracted toolchains, and cache outputs are excluded from authored
source and are reproducible from recorded official URLs and SHA256 digests.
The artifact review must cover all authored helpers against one fixed source
baseline, both independent axes, actual test results, and final delivered-file
identity. No formal candidate is accepted by this operational tooling review.
