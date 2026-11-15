#!/usr/bin/env python3
"""Exercise parsing, offline evidence and actual clients through the JSON driver."""
import copy
import json
import unittest

from choice_driver_client import Session

SESSION = None


def request(value):
    return SESSION.request(value)


class ChoiceDriverTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        global SESSION
        SESSION = Session()

    @classmethod
    def tearDownClass(cls):
        SESSION.close()

    def test_nested_admission_uses_completed_context(self):
        result = request({"client": "scan", "depthLimit": 4})
        self.assertEqual(result["status"], "ok")
        self.assertEqual(result["chosen"], result["context"]["catalog"][0])
        self.assertEqual(len(result["context"]["catalog"]), 1)
        self.assertFalse(result["evidenceUsed"])

    def test_offline_records_reload_and_change_scan_choice(self):
        base = {"client": "scan"}
        initial = request(base)
        context = initial["context"]
        first, second = initial["context"]["catalog"]
        self.assertEqual(initial["chosen"], first)
        epoch = None
        for candidate, elapsed in [(first, 20), (second, 10)]:
            response = request(dict(base, mode="record", evidence=epoch,
                                    sample={"candidate": candidate, "repetition": 0,
                                            "elapsedNs": elapsed, "success": True, "context": context}))
            self.assertEqual(response["status"], "ok", response)
            epoch = response["epoch"]
        # JSON roundtrip models saving and loading an immutable epoch.
        loaded = json.loads(json.dumps(epoch))
        result = request(dict(base, mode="run", evidence=loaded))
        self.assertEqual(result["chosen"], second)
        self.assertTrue(result["evidenceUsed"])
        self.assertEqual(result["execution"]["outputs"], [0, 0, 1, 3, 6, 10, 15, 21, 28])
        self.assertEqual(result["execution"]["total"], 36)

    def test_tree_realizations_use_same_evidence_path(self):
        base = {"client": "tree", "variant": "star", "nodes": 4, "queries": 4}
        initial = request(base)
        context = initial["context"]
        self.assertEqual(initial["context"]["catalog"], ["direct", "sparse"])
        fixed = initial["chosen"]
        other = "sparse" if fixed == "direct" else "direct"
        epoch = None
        for candidate, elapsed in [(fixed, 20), (other, 10)]:
            epoch = request(dict(base, mode="record", evidence=epoch,
                                 sample={"candidate": candidate, "repetition": 0,
                                         "elapsedNs": elapsed, "success": True, "context": context}))["epoch"]
        trained = request(dict(base, mode="run", evidence=epoch))
        baseline = request(dict(base, mode="run"))
        self.assertEqual(trained["chosen"], other)
        self.assertTrue(trained["evidenceUsed"])
        self.assertEqual(trained["execution"]["outputs"], [0, 0, 0, 0])
        self.assertEqual(trained["execution"]["outputs"], baseline["execution"]["outputs"])
        self.assertEqual(trained["execution"]["queryNs"], 0)  # run reads no clock

    def test_imported_epochs_are_validated_before_ranking(self):
        base = {"client": "scan"}
        initial = request(base)
        context = initial["context"]
        first, second = initial["context"]["catalog"]
        epoch = {"context": copy.deepcopy(context), "repetitions": 1,
                 "samples": [{"candidate": first, "repetition": 0, "elapsedNs": 20,
                              "success": True, "context": copy.deepcopy(context)},
                             {"candidate": second, "repetition": 0, "elapsedNs": 10,
                              "success": True, "context": copy.deepcopy(context)}]}
        self.assertEqual(request(dict(base, evidence=epoch))["chosen"], second)
        corruptions = []
        for key in ("implementation", "target", "workload", "site", "protocol"):
            bad = copy.deepcopy(epoch)
            bad["context"][key] += "-changed"
            corruptions.append((key, bad))
        bad = copy.deepcopy(epoch)
        bad["context"]["requirements"] = [999]
        corruptions.append(("constraints", bad))
        for name, change in [
            ("missing", lambda e: e["samples"].pop()),
            ("duplicate", lambda e: e["samples"].append(copy.deepcopy(e["samples"][0]))),
            ("duplicate-with-same-length", lambda e: e["samples"].__setitem__(1, copy.deepcopy(e["samples"][0]))),
            ("unknown", lambda e: e["samples"][0].update(candidate="unknown")),
            ("failed", lambda e: e["samples"][0].update(success=False)),
            ("misstamped", lambda e: e["samples"][0]["context"].update(workload="other")),
            ("out-of-range", lambda e: e["samples"][0].update(repetition=1)),
            ("zero-repetitions", lambda e: e.update(repetitions=0)),
            ("duplicate-ID", lambda e: e["context"]["catalog"].append(first)),
        ]:
            bad = copy.deepcopy(epoch)
            change(bad)
            if name == "misstamped":
                self.assertEqual(bad["context"], context)
            corruptions.append((name, bad))
        for name, bad in corruptions:
            with self.subTest(name=name):
                result = request(dict(base, evidence=bad))
                self.assertEqual(result["chosen"], first)
                self.assertFalse(result["evidenceUsed"])
        tied = copy.deepcopy(epoch)
        tied["samples"][1]["elapsedNs"] = 20
        self.assertEqual(request(dict(base, evidence=tied))["chosen"], first)
        changed = request(dict(base, evidence=epoch, seed=1))
        self.assertFalse(changed["evidenceUsed"])
        self.assertEqual(changed["chosen"], first)
        constrained = request(dict(base, evidence=epoch, depthLimit=4))
        self.assertEqual(constrained["chosen"], second)
        self.assertFalse(constrained["evidenceUsed"])
        self.assertIsNone(request(dict(base, evidence=epoch, depthLimit=3))["chosen"])

    def test_record_rejects_duplicate_failed_and_unknown_observations(self):
        base = {"client": "scan"}
        context = request(base)["context"]
        first = context["catalog"][0]
        sample = {"candidate": first, "repetition": 0, "elapsedNs": 20, "success": True, "context": context}
        epoch = request(dict(base, mode="record", sample=sample))["epoch"]
        duplicate = request(dict(base, mode="record", sample=sample, evidence=epoch))
        self.assertEqual(duplicate["status"], "error")
        for update in ({"candidate": "unknown"}, {"success": False}, {"repetition": 1}):
            with self.subTest(update=update):
                result = request(dict(base, mode="record", sample=dict(sample, **update)))
                self.assertEqual(result["status"], "error")
        mismatch = copy.deepcopy(epoch)
        mismatch["context"]["target"] = "different"
        self.assertEqual(request(dict(base, mode="record", sample=sample, evidence=mismatch))["status"], "error")
        self.assertFalse(request(dict(base, evidence=epoch))["evidenceUsed"])

    def test_malformed_requests_are_rejected_and_next_request_still_runs(self):
        for text in ("{", "[]", '{"client":"scan","repetitions":-1}',
                     '{"client":"scan","evidence":{"samples":[]}}'):
            with self.subTest(text=text):
                self.assertEqual(SESSION.raw(text)["status"], "error")
        for update in ({"mode": "unknown"}, {"client": "unknown"}, {"repetitions": 0},
                       {"repetitions": 21}, {"power": 9}, {"depthLimit": "4"}):
            self.assertEqual(request(dict({"client": "scan"}, **update))["status"], "error")
        self.assertEqual(request({"client": "scan"})["status"], "ok")

    def test_realization_execution_and_empty_admission(self):
        for variant, nodes, count in [("star", 17, 32), ("chain", 65, 32), ("branching", 65, 32)]:
            base = {"client": "tree", "variant": variant, "nodes": nodes, "queries": count}
            for candidate in ["direct", "sparse"]:
                with self.subTest(variant=variant, candidate=candidate):
                    result = request(dict(base, mode="explore", candidate=candidate))
                    self.assertEqual(result["status"], "ok", result)
                    self.assertEqual(len(result["execution"]["outputs"]), count)
                    self.assertEqual(result["executed"], candidate)
            self.assertIsNone(request(dict(base, capacity=0))["chosen"])
            self.assertEqual(request(dict(base, capacity=0, mode="explore", candidate="direct"))["status"], "error")
        for power in [4, 6, 8]:
            base = {"client": "scan", "variant": "powers", "power": power}
            for candidate in request(base)["context"]["catalog"]:
                result = request(dict(base, mode="explore", candidate=candidate))
                self.assertEqual(result["status"], "ok", result)
                self.assertEqual(len(result["execution"]["outputs"]), 2**power)
        self.assertIsNone(request({"client": "scan", "mode": "run", "depthLimit": 3})["execution"])

    def test_equal_repetition_totals_rank_all_samples(self):
        base = {"client": "scan", "repetitions": 2}
        initial = request(base)
        context = initial["context"]
        first, second = initial["context"]["catalog"]
        epoch = {"context": initial["context"], "repetitions": 2, "samples": []}
        for candidate, values in [(first, [1, 100]), (second, [60, 60])]:
            for repetition, elapsed in enumerate(values):
                epoch["samples"].append({"candidate": candidate, "repetition": repetition,
                                         "elapsedNs": elapsed, "success": True, "context": context})
        result = request(dict(base, evidence=epoch))
        self.assertTrue(result["evidenceUsed"])
        self.assertEqual(result["chosen"], first)  # 101 < 120, despite the last sample being slower.

    def test_observation_context_cannot_be_relabelled_by_current_request(self):
        base = {"client": "scan"}
        context = request(base)["context"]
        old_context = copy.deepcopy(context)
        old_context["workload"] += "-different"
        sample = {"candidate": context["catalog"][0], "repetition": 0,
                  "elapsedNs": 5, "success": True, "context": old_context}
        result = request(dict(base, mode="record", sample=sample))
        self.assertEqual(result["status"], "error")


if __name__ == "__main__":
    unittest.main()
