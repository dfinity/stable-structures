#!/usr/bin/python3
import re
import csv
import sys

def parse_benchmarks(file_content):
    """
    Parse the benchmark file content and extract benchmark names with their instructions count.
    The function expects lines like:
      Benchmark: btreemap_get_blob_4_4_v2
      ... instructions: 249.10 M ...
    It converts the number with its multiplier (K, M, or B) into an integer.
    """
    pattern = re.compile(
        r'Benchmark:\s+(?P<name>[^\n]+).*?instructions:\s+(?P<number>[\d\.]+)\s*(?P<unit>[KMB])',
        re.DOTALL
    )
    benchmarks = []
    for match in pattern.finditer(file_content):
        name = match.group('name').strip()
        num_str = match.group('number').strip()
        unit = match.group('unit').strip()

        # Convert string to float and apply multiplier.
        multiplier = {'K': 1e3, 'M': 1e6, 'B': 1e9}.get(unit, 1)
        instructions = int(float(num_str) * multiplier)
        benchmarks.append((name, instructions))
    return benchmarks

def split_versions(benchmarks):
    """
    Splits the benchmark data into two dictionaries:
    - data_v1 for benchmarks without the "_v2" suffix.
    - data_v2 for benchmarks with the "_v2" suffix.
    
    Each dictionary maps a tuple (key_size, value_size) to its instructions count.
    Only benchmark names that exactly match the pattern are processed.
    The expected benchmark name formats are:
      btreemap_get_blob_<key>_<value>
      btreemap_get_blob_<key>_<value>_v2
    Names with extra suffixes (e.g. _mem_manager) are ignored.
    """
    data_v1 = {}
    data_v2 = {}
    # Regex to extract key and value sizes and check for version suffix.
    # The pattern now uses ^ and $ anchors to ensure the entire name matches.
    pattern = re.compile(r'^btreemap_get_blob_(?P<key>\d+)_(?P<value>\d+)(?P<version>_v2)?$')
    
    for name, instructions in benchmarks:
        m = pattern.search(name)
        if m:
            key_size = int(m.group('key'))
            value_size = int(m.group('value'))
            if m.group('version'):
                data_v2[(key_size, value_size)] = instructions
            else:
                data_v1[(key_size, value_size)] = instructions
    return data_v1, data_v2

def write_csv(data, filename):
    """
    Writes a CSV file where:
    - The header row contains the key sizes (columns).
    - The first column of each row contains the value size.
    - Each cell contains the instructions count (or empty if not available).
    """
    # Determine all unique key sizes and value sizes from the data
    key_sizes = sorted({k for (k, v) in data.keys()})
    value_sizes = sorted({v for (k, v) in data.keys()})
    
    with open(filename, 'w', newline='') as csvfile:
        writer = csv.writer(csvfile, delimiter='\t')
        # Write header row: first column header then sorted key sizes
        header = ['Value/Key'] + [str(ks) for ks in key_sizes]
        writer.writerow(header)
        
        # Write each row for every unique value size
        for vs in value_sizes:
            row = [str(vs)]
            for ks in key_sizes:
                cell_value = data.get((ks, vs), '')
                row.append(str(cell_value))
            writer.writerow(row)

def main(input_file):
    with open(input_file, 'r') as f:
        content = f.read()
    
    benchmarks = parse_benchmarks(content)
    data_v1, data_v2 = split_versions(benchmarks)
    
    write_csv(data_v1, 'v1.csv')
    write_csv(data_v2, 'v2.csv')
    
    print("CSV files 'v1.csv' and 'v2.csv' have been generated.")

if __name__ == '__main__':
    if len(sys.argv) != 2:
        print("Usage: python script.py <input_file>")
        sys.exit(1)
    main(sys.argv[1])
