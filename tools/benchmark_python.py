"""Benchmark two Python decompilers and verify every output against a reference.

Uses an existing output directory seeded from the reference before timing,
warms the input cache, and alternates run order. Each timed CLI invocation
includes process startup, decompilation, and file writes; hashing is untimed.
The work directory must be new. No existing dumps are changed or deleted.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import statistics
import subprocess
import sys
import time


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def file_map(root: Path, extension: str) -> dict[str, Path]:
    result = {}
    for path in root.rglob('*'):
        if path.is_file() and path.suffix.lower() == extension:
            key = path.relative_to(root).with_suffix('.lua').as_posix().casefold()
            if key in result:
                raise ValueError(f'Duplicate output name: {key}')
            result[key] = path
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', type=Path, required=True)
    parser.add_argument('--candidate', type=Path, default=Path(__file__).resolve().parents[1] / 'luajit-decompiler.py')
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--reference', type=Path, required=True)
    parser.add_argument('--work-dir', type=Path, required=True)
    parser.add_argument('--workers', type=int, nargs='+', default=[1, 12])
    parser.add_argument('--repeats', type=int, default=3)
    args = parser.parse_args()
    if args.repeats < 1 or any(workers < 1 for workers in args.workers):
        parser.error('Workers and repeats must be positive')
    scripts = {'baseline': args.baseline.resolve(), 'optimized': args.candidate.resolve()}
    input_root, reference = args.input.resolve(), args.reference.resolve()
    inputs = file_map(input_root, '.luac')
    goldens = file_map(reference, '.lua')
    if not inputs or inputs.keys() != goldens.keys():
        raise ValueError('Input and reference must have the same nonempty set of relative names')
    root = args.work_dir.resolve()
    if root.is_relative_to(input_root) or root.is_relative_to(reference):
        raise ValueError('Benchmark output must be outside the input and reference trees')
    root.mkdir(parents=True, exist_ok=False)
    output = root / 'output'
    expected = {}
    output_paths = []
    for key, source in inputs.items():
        source.read_bytes()  # Warm the input cache outside the measured interval.
        data = goldens[key].read_bytes()
        expected[key] = hashlib.sha256(data).hexdigest()
        target = (output / source.relative_to(input_root)).with_suffix('.lua')
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        output_paths.append(target)
    report = {
        'python': sys.version, 'platform': platform.platform(),
        'logical_cpus': os.cpu_count(), 'input': str(input_root),
        'reference': str(reference), 'files': len(inputs),
        'input_bytes': sum(path.stat().st_size for path in inputs.values()),
        'scripts': {label: {'path': str(path), 'sha256': digest(path)}
                    for label, path in scripts.items()},
        'flags': ['-e', '.luac', '-m', '-f'],
        'method': 'warm cache; same output paths; alternating order; stdout/stderr to logs; hash checks outside timing',
        'runs': [],
    }
    report_path = root / 'results.json'

    def save() -> None:
        report_path.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')

    save()
    for workers in args.workers:
        for repeat in range(args.repeats):
            order = ['baseline', 'optimized'] if repeat % 2 == 0 else ['optimized', 'baseline']
            for label in order:
                script = scripts[label]
                if digest(script) != report['scripts'][label]['sha256']:
                    raise AssertionError(f'{label} changed during the benchmark')
                # Old timestamps ensure a failed worker cannot pass by leaving
                # behind a matching output from the previous successful run.
                for path in output_paths:
                    os.utime(path, (946684800, 946684800))
                log = root / f'{label}-w{workers}-r{repeat + 1}.log'
                command = [sys.executable, str(script), str(input_root), '-o', str(output),
                           *report['flags'], '--workers', str(workers)]
                print(f'START {label} workers={workers} repeat={repeat + 1}', flush=True)
                with log.open('wb') as stream:
                    started = time.perf_counter()
                    process = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT, timeout=1800)
                    elapsed = time.perf_counter() - started
                actual = file_map(output, '.lua')
                missing = sorted(expected.keys() - actual.keys())
                extra = sorted(actual.keys() - expected.keys())
                different = []
                stale = []
                for key in expected.keys() & actual.keys():
                    path = actual[key]
                    if digest(path) != expected[key]:
                        different.append(key)
                    if path.stat().st_mtime < 946684801:
                        stale.append(key)
                run = {
                    'version': label, 'workers': workers, 'repeat': repeat + 1,
                    'seconds': elapsed, 'returncode': process.returncode,
                    'output_files': len(actual), 'missing': missing, 'extra': extra,
                    'different': different, 'stale': stale, 'log': str(log),
                }
                report['runs'].append(run)
                save()
                if process.returncode or missing or extra or different or stale:
                    raise AssertionError(f'Output validation failed; see {report_path} and {log}')
                print(f'PASS {label} workers={workers} repeat={repeat + 1}: '
                      f'{elapsed:.3f}s; {len(actual)} identical files', flush=True)
    report['summary'] = []
    for workers in args.workers:
        medians = {}
        for label in scripts:
            times = [run['seconds'] for run in report['runs']
                     if run['workers'] == workers and run['version'] == label]
            medians[label] = statistics.median(times)
        report['summary'].append({
            'workers': workers, 'median_seconds': medians,
            'speedup': medians['baseline'] / medians['optimized'],
            'time_reduction_percent': 100 * (1 - medians['optimized'] / medians['baseline']),
        })
    save()
    print(json.dumps(report['summary'], indent=2), flush=True)


if __name__ == '__main__':
    main()
