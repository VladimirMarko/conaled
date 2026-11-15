#!/usr/bin/env python3
"""Summarize Lean/Lake warning occurrences; compare counts without changing acceptance."""
import argparse
from collections import Counter
import json
from pathlib import Path
import re
import sys

ANSI = re.compile(r'\x1b\[[0-?]*[ -/]*[@-~]')
LEAN = re.compile(r'^(.*?\.lean)(?::\d+:\d+)?:\s*warning:\s*(.*)$')
LAKE = re.compile(r'^warning:\s*(.*?\.lean)(?::\d+:\d+)?:\s*(.*)$')
CATEGORIES = (
    ('This simp argument is unused', 'unused-simp-argument'),
    ('automatically included section variable', 'unused-section-variable'),
    ('Unused tactic linter', 'unused-tactic'),
    ('this tactic is never executed', 'unreachable-tactic'),
    ('`simp` already closes the goal', 'unnecessary-simpa'),
    ('Used `tac1 <;> tac2`', 'unnecessary-sequence'),
    ('Variable name ', 'unused-variable'),
    ('of class type is semireducible', 'definition-reducibility'),
    ('is a proposition; use `theorem`', 'definition-is-proposition'),
    ('which is designed for use with the module system', 'module-import'),
    ('Try this:', 'suggestion'),
    ('declaration uses `sorry`', 'admission'),
    ("declaration uses 'sorry'", 'admission'),
)


def summarize(path):
    pairs = Counter()
    with path.open(encoding='utf-8', errors='replace') as stream:
        for line in stream:
            line = ANSI.sub('', line).strip()
            match = LEAN.match(line) or LAKE.match(line)
            if match:
                module, message = match.groups()
                while module.startswith('./'):
                    module = module[2:]
                module = module.removesuffix('.lean').replace('/', '.')
            elif line.startswith('warning:'):
                module, message = '<unknown>', line[len('warning:'):].strip()
            else:
                continue
            category = next((name for text, name in CATEGORIES if text in message), 'other')
            pairs[module, category] += 1
    modules, categories = Counter(), Counter()
    for (module, category), count in pairs.items():
        modules[module] += count
        categories[category] += count
    return {
        'format': 1, 'warnings': sum(pairs.values()),
        'by_module': dict(sorted(modules.items())), 'by_category': dict(sorted(categories.items())),
        'by_module_category': [{'module': m, 'category': c, 'count': n}
                               for (m, c), n in sorted(pairs.items())],
    }, pairs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('log', type=Path)
    parser.add_argument('--baseline', type=Path, help='earlier log for per-module/category count differences')
    args = parser.parse_args()
    report, current = summarize(args.log)
    if args.baseline:
        baseline, previous = summarize(args.baseline)
        report['comparison'] = {
            'baseline_warnings': baseline['warnings'],
            'delta': report['warnings'] - baseline['warnings'],
            'changes': [{'module': m, 'category': c, 'delta': current[m, c] - previous[m, c]}
                        for m, c in sorted(current.keys() | previous.keys())
                        if current[m, c] != previous[m, c]],
        }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except OSError as error:
        print(f'Warning summary failed: {error}', file=sys.stderr)
        sys.exit(1)
