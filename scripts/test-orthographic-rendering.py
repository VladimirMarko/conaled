#!/usr/bin/env python3
"""Exercise the actual Lean IO boundary against independently worked pixel bands."""
import pathlib
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]


class OrthographicOutput(unittest.TestCase):
    def test_asymmetric_raster_order(self):
        with tempfile.TemporaryDirectory(prefix="orthographic fixture ") as tmp:
            fixture = pathlib.Path(tmp) / "fixture.lean"
            fixture.write_text("""import Examples.OrthographicRendering
open Applications.Rendering.PPM Examples.OrthographicRendering
def main : IO Unit := IO.print (rasterText asymmetricRaster)
""")
            result = subprocess.run(["lake", "env", "lean", "--run", str(fixture)],
                                    cwd=ROOT, check=True, text=True, capture_output=True)
            self.assertEqual(result.stdout, "255 0 0\n0 255 0\n0 0 255\n1 2 3\n")

    def test_sequence(self):
        with tempfile.TemporaryDirectory(prefix="orthographic output ") as tmp:
            output = pathlib.Path(tmp) / "nested" / "frames"
            subprocess.run(["lake", "env", "lean", "--run",
                            "scripts/render-orthographic.lean", str(output)],
                           cwd=ROOT, check=True)
            self.assertEqual(sorted(p.name for p in output.iterdir()),
                             [f"frame-{k:03}.ppm" for k in range(3)])
            frames = []
            for k, (far_start, near_start) in enumerate([(12, 16), (8, 12), (4, 8)]):
                data = (output / f"frame-{k:03}.ppm").read_text(encoding="ascii")
                tokens = data.split()
                self.assertEqual(tokens[:4], ["P3", "32", "32", "255"])
                channels = list(map(int, tokens[4:]))
                self.assertEqual(len(channels), 32 * 32 * 3)
                self.assertTrue(all(0 <= c <= 255 for c in channels))
                pixels = list(zip(channels[::3], channels[1::3], channels[2::3]))
                # Independent integer rectangles derived from the issue's center coordinates.
                for row in range(32):
                    for col in range(32):
                        expected = (0, 0, 0)
                        if 8 <= row <= 23 and far_start <= col < far_start + 16:
                            expected = (0, 127, 0)
                            if near_start <= col < near_start + 8:
                                expected = (127, 63, 0)
                        self.assertEqual(pixels[row * 32 + col], expected, (k, row, col))
                self.assertEqual(pixels.count((127, 63, 0)), 128)
                self.assertEqual(pixels.count((0, 127, 0)), 128)
                self.assertEqual(pixels.count((0, 0, 0)), 768)
                frames.append(data)
            self.assertEqual(len(set(frames)), 3)
            # Re-running in the same caller-selected directory deterministically replaces files.
            subprocess.run(["lake", "env", "lean", "--run",
                            "scripts/render-orthographic.lean", str(output)],
                           cwd=ROOT, check=True)
            self.assertEqual(frames, [(output / f"frame-{k:03}.ppm").read_text()
                                     for k in range(3)])


if __name__ == "__main__":
    unittest.main()
