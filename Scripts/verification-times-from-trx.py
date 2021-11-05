#!/usr/bin/env python3
 
import xml.etree.ElementTree as ET
import sys
import os

def results_for_trx_file(file):
    return ET.parse(file).getroot().find("./{http://microsoft.com/schemas/VisualStudio/TeamTest/2010}Results") 

def print_sorted_results(results):
    sorted_by_duration = sorted(results, key=lambda result: result.attrib.get("duration", "00:00:00.0000000"), reverse=True)
    sorted_by_outcome_then_duration = sorted(sorted_by_duration, key=lambda result: result.attrib["outcome"] == "passed")
    for result in sorted_by_outcome_then_duration:
        print(f'{result.attrib["duration"]}s ({result.attrib["outcome"]}) - {result.attrib["testName"]}')

path = sys.argv[1]
files = [path]
if os.path.isdir(path):
    files = [os.path.join(path, f) for f in os.listdir(path) if f.endswith('.trx')]
all_results = [result for file in files for results in results_for_trx_file(file) for result in results]

print_sorted_results(all_results)