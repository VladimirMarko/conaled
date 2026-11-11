#!/usr/bin/env python3
"""Black-box checks against independently calculated finite action fixtures."""
import json
from pathlib import Path
import subprocess
import unittest
import tempfile
import sys
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parents[1]


class Diagrams(unittest.TestCase):
    def test_export(self):
        result = subprocess.run(
            ["lake", "env", "lean", "--run", "scripts/schreier-diagrams.lean"],
            cwd=ROOT, text=True, capture_output=True, check=True,
        )
        actual = json.loads(result.stdout)
        expected = json.loads((ROOT / "tests/fixtures/schreier-diagrams.json").read_text())
        self.assertEqual([d["name"] for d in actual], list(expected))
        for diagram in actual:
            fixture = expected[diagram["name"]]
            self.assertEqual(diagram["vertices"], [
                {"id": i, "label": label} for i, label in enumerate(fixture["vertices"])])
            self.assertEqual(diagram["generators"], [
                {"id": i, "label": label} for i, label in enumerate(fixture["labels"])])
            rows = [{"id": f"{v}:{s}", "source": v, "target": target,
                     "generator": s, "label": fixture["labels"][s]}
                    for v, targets in enumerate(fixture["targets"])
                    for s, target in enumerate(targets)]
            self.assertEqual(diagram["edges"], rows)


    def test_lean_serialization_escapes_display_text(self):
        result = subprocess.run(
            ["lake", "env", "lean", "--run", "tests/fixtures/schreier-escaping.lean"],
            cwd=ROOT, capture_output=True, text=True, check=True)
        data = json.loads(result.stdout)
        self.assertEqual(data["name"], 'A < B & "C"')
        self.assertEqual(data["vertices"], [{"id": 0, "label": 'line\n"quoted"\\tail<&>'}])
        self.assertEqual(len(data["edges"]), 3)

    def test_saved_artifacts(self):
        result = subprocess.run(
            ["lake", "env", "lean", "--run", "scripts/schreier-diagrams.lean"],
            cwd=ROOT, capture_output=True, check=True)
        saved = ROOT / "docs/diagrams/schreier"
        self.assertEqual(result.stdout, (saved / "actions.json").read_bytes())
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory) / "actions.svg"
            subprocess.run([sys.executable, str(ROOT / "scripts/render-schreier-diagrams.py"),
                            str(saved / "actions.json"), str(target)], check=True)
            self.assertEqual(target.read_bytes(), (saved / "actions.svg").read_bytes())
            tree = ET.parse(target)
            ns = {"s": "http://www.w3.org/2000/svg"}
            for diagram in json.loads(result.stdout):
                panel = tree.find(f".//s:g[@data-diagram='{diagram['name']}']", ns)
                rendered = panel.findall("s:g[@class='edge']", ns)
                expected = {edge["id"]: edge for edge in diagram["edges"]}
                self.assertEqual(len(rendered), len(expected))
                self.assertEqual({edge.get("data-edge-id") for edge in rendered}, set(expected))
                paths = []
                for edge in rendered:
                    original = expected[edge.get("data-edge-id")]
                    for field in ("source", "target", "generator"):
                        self.assertEqual(edge.get(f"data-{field}"), str(original[field]))
                    path = edge.find("s:path", ns)
                    self.assertTrue(path.get("marker-end"))
                    paths.append(path.get("d"))
                self.assertEqual(len(set(paths)), len(paths))

    def test_render_preserves_rows_and_escapes(self):
        # A hand-written fixture: two distinct labels and one repeated value,
        # all with identical endpoints. It also exercises XML-sensitive text.
        diagram = [{"name": 'A < B & "C"',
                    "vertices": [{"id": 0, "label": "<&>"}],
                    "generators": [{"id": 0, "label": "<&>"},
                                   {"id": 1, "label": "other"},
                                   {"id": 2, "label": "<&>"}],
                    "edges": [{"id": f"0:{s}", "source": 0, "target": 0,
                               "generator": s, "label": label}
                              for s, label in enumerate(["<&>", "other", "<&>"])]}]
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "input.json"
            target = Path(directory) / "output.svg"
            source.write_text(json.dumps(diagram))
            command = [sys.executable, str(ROOT / "scripts/render-schreier-diagrams.py"),
                       str(source), str(target)]
            subprocess.run(command, check=True, capture_output=True)
            first = target.read_bytes()
            subprocess.run(command, check=True, capture_output=True)
            self.assertEqual(first, target.read_bytes())
            tree = ET.fromstring(first)
            ns = {"s": "http://www.w3.org/2000/svg"}
            edges = tree.findall(".//s:g[@class='edge']", ns)
            self.assertEqual([e.get("data-edge-id") for e in edges], ["0:0", "0:1", "0:2"])
            paths = [e.find("s:path", ns) for e in edges]
            self.assertEqual(len({p.get("d") for p in paths}), 3)
            self.assertTrue(all(p.get("marker-end") for p in paths))
            self.assertIn("<&>", [e.text for e in tree.findall(".//s:text", ns)])
            self.assertIn('A < B & "C"', [e.text for e in tree.findall(".//s:text", ns)])


if __name__ == "__main__":
    unittest.main()
