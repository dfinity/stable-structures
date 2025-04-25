#!/usr/bin/env python3
import re
import sys
import csv
import logging
from itertools import product

CHANGE_RE = re.compile(r'^(improved|regressed)\s+by\s+([\d.]+)%\s*$', re.IGNORECASE)
def parse_change(text):
    m = CHANGE_RE.match(text or '')
    if not m:
        return 0.0
    direction, fraction = m.group(1).lower(), float(m.group(2)) / 100.0
    return -fraction if direction == 'improved' else fraction


METRIC_RE = re.compile(
    r'^\s*(?P<name>[^:]+):\s*'
    r'(?P<value>[\d.]+)\s*(?P<unit>\w+)'
    r'(?:\s*\((?P<change>[^)]+)\))?'
)
def parse_metric(line):
    m = METRIC_RE.match(line)
    if m:
        change = m.group('change')
        #print(change)
        return (
            m.group('name').strip(),
            float(m.group('value')),
            m.group('unit'),
            parse_change(change)
        )


BENCHMARK_RE = re.compile(r'^\s*Benchmark:\s+(?P<name>.+?)(\s*\(new\))?\s*$')
UNIT_MULTIPLIERS = {'K': 10**3, 'M': 10**6, 'B': 10**9}
METRICS = {
    'instructions':           ('instructions', UNIT_MULTIPLIERS),
    'heap_increase':          ('heap_increase', 1),
    'stable_memory_increase': ('stable_memory_increase', 1),
}
def parse_bench_blocks(lines):
    benchmarks = []
    current = None

    for line in lines:
        bm = BENCHMARK_RE.match(line)
        if bm:
            if current:
                benchmarks.append(current)
            current = {'name': bm.group('name').strip()}
            continue

        if not current:
            continue

        parsed = parse_metric(line)
        if not parsed:
            continue

        name, val, unit, change = parsed
        info = METRICS.get(name)
        if not info:
            continue

        field, mult = info
        factor = mult.get(unit, 1) if isinstance(mult, dict) else mult
        value = int(val * factor)

        if value:
            current[field] = {'value': value, 'change': change}

    if current:
        benchmarks.append(current)
    return benchmarks

BENCH_PREFIX_RE = re.compile(
    r'btreemap_v(?P<version>\d+)'
    r'(?P<mem_manager>_mem_manager)*'
    r'_(?P<remaining>\w+)'
)
FUNCTIONS = [
    'insert', 'remove', 'get', 'contains', 'scan', 'pop_first', 'pop_last'
]
_FUNCS_PATTERN = "|".join(map(re.escape, FUNCTIONS))
BENCH_FUNC_RE = re.compile(
    rf"(?P<func>{_FUNCS_PATTERN})_(?P<remaining>\w+)?"
)
BENCH_TYPE_KEY_VALUE_RE = re.compile(
    r'(?P<type>blob|vec)'
    r'_(?P<k_size>\d+)'
    r'_(?P<v_size>\d+)'
)
BENCH_TYPES_A_B_RE = re.compile(
    r'(?P<type_a>u\d+|blob\d+|vec\d+)'
    r'_(?P<type_b>u\d+|blob\d+|vec\d+)'
)


def parse_bench_by_name(bench):
    m = BENCH_PREFIX_RE.match(bench['name'])
    if m:
        data = {
            'name': bench['name'],
            'version': int(m.group('version')),
            'mem_manager': len(m.group('mem_manager') or '') > 0,
            'instructions': bench['instructions']['value'],
            'instructions_change': bench['instructions']['change'],
        }

        m = BENCH_FUNC_RE.match(m.group('remaining'))
        if m:
            data['func'] = m.group('func')

            remaining = m.group('remaining')
            m = BENCH_TYPE_KEY_VALUE_RE.match(remaining)
            if m:
                data.update({
                    'schema': 'type-key-value',
                    'type': m.group('type'),
                    'key_size': int(m.group('k_size')),
                    'value_size': int(m.group('v_size')),
                })
                return data
            
            m = BENCH_TYPES_A_B_RE.match(remaining)
            if m:
                data.update({
                    'schema': 'types-a-b',
                    'type_a': m.group('type_a'),
                    'type_b': m.group('type_b'),
                })
                return data


def load_benchmarks(path, verbose=False, logger=None):
    logger = logger or logging.getLogger(__name__)
    out = []
    with open(path) as f:
        for block in parse_bench_blocks(f):
            parsed = parse_bench_by_name(block)
            if parsed:
                out.append(parsed)
                if verbose:
                    logger.info(f"Parsed: {parsed}")
            elif verbose:
                logger.warning(f"Failed to parse: {block['name'].strip()!r}")
    return out


def save_all_tables(tables, sizes, filename):
    fmt_instr = lambda v: "" if v is None else '{:.3f}'.format(v / 1e9)
    fmt_change = lambda v: "" if v is None else '{:.1f}%'.format(v * 100.0)

    with open(filename, 'w', newline='') as f:
        writer = csv.writer(f, delimiter='\t')
        for tbl in tables:
            writer.writerow([tbl['name']])
            writer.writerow(['{} | {}'.format(tbl['rows'], tbl['columns'])] + sizes + [''] + sizes)
            instr, change = tbl['instructions'], tbl['instructions_change']
            for r in sizes:
                writer.writerow(
                    [r]
                    + [fmt_instr(instr[r][c]) for c in sizes]
                    + ['']
                    + [fmt_change(change[r][c]) for c in sizes]
                )
            writer.writerow([])


def main():
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} <input_file>")
        sys.exit(1)

    logging.basicConfig(level=logging.WARNING, format="%(levelname)s: %(message)s")
    logger = logging.getLogger(__name__)
    benchmarks = load_benchmarks(sys.argv[1], verbose=True, logger=logger)

    used = set()
    all_tables = []
    for version, func in product(
            [2, 1],
            FUNCTIONS,
        ):

        # Big tables blob/vec 4-1024
        for type_ in ['blob', 'vec']:
            size_grid = [4, 8, 16, 32, 64, 128, 256, 512, 1024]
            name = f'btreemap_v{version}_{func}_{type_}'
            table = {
                'name': name,
                'columns': 'keys',
                'rows': 'values',
                'instructions': {r: {c: None for c in size_grid} for r in size_grid},
                'instructions_change': {r: {c: None for c in size_grid} for r in size_grid}
            }
            for key_size in size_grid:
                for value_size in size_grid:
                    filters = {
                        'version': version,
                        'mem_manager': False,
                        'func': func,
                        'schema': 'type-key-value',
                        'type': type_,
                        'key_size': key_size,
                        'value_size': value_size,
                    }
                    selected = [
                        b for b in benchmarks
                        if all(b.get(k) == v for k, v in filters.items())
                    ]
                    if len(selected) == 0:
                        continue
                    if len(selected) > 1:
                        logger.error(f"Multiple matches for {filters}: {selected}")
                        continue
                    data = selected[0] if selected else None
                    table['instructions'][value_size][key_size] = data['instructions'] if data else None
                    table['instructions_change'][value_size][key_size] = data['instructions_change'] if data else None
                    used.add(data['name']) if data else None

            has_any = any(
                cell is not None
                for row in table['instructions'].values()
                for cell in row.values()
            )
            if has_any:
                all_tables.append(table)
        
        # Small tables u64/blob/vec 8-512
        name = f'btreemap_v{version}_{func}'
        type_grid = ['u64', 'blob8', 'vec8', 'blob512', 'vec512']
        table = {
            'name': name,
            'columns': 'keys',
            'rows': 'values',
            'instructions': {r: {c: None for c in size_grid} for r in size_grid},
            'instructions_change': {r: {c: None for c in size_grid} for r in size_grid}
        }
        for key, value, mem_manager in product(
            type_grid,
            type_grid,
            [False, True],
        ):
            filters = {
                'version': version,
                'mem_manager': mem_manager,
                'func': func,
                'schema': 'types-a-b',
                'type_a': key,
                'type_b': value,
            }
            selected = [
                b for b in benchmarks
                if all(b.get(k) == v for k, v in filters.items())
            ]
            if len(selected) == 0:
                continue
            if len(selected) > 1:
                logger.error(f"Multiple matches for {filters}: {selected}")
                continue
            data = selected[0] if selected else None
            table['instructions'][value_size][key_size] = data['instructions'] if data else None
            table['instructions_change'][value_size][key_size] = data['instructions_change'] if data else None
            used.add(data['name']) if data else None

        has_any = any(
            cell is not None
            for row in table['instructions'].values()
            for cell in row.values()
        )
        if has_any:
            all_tables.append(table)

    for bench in benchmarks:
        if bench['name'] not in used:
            logger.warning(f"Unused benchmark: {bench['name']}")

    save_all_tables(all_tables, size_grid, './tmp/all_benchmarks.csv')


if __name__ == '__main__':
    main()
