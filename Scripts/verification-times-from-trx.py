#!/usr/bin/env python3
 
import xml.etree.ElementTree as ET
import sys

def results_for_trx_file(file):
    return ET.parse(file).getroot().find("./{http://microsoft.com/schemas/VisualStudio/TeamTest/2010}Results") or []

results = [result for file in sys.argv[1:] for result in results_for_trx_file(file)]
sorted_by_duration = sorted(results, key=lambda result: result.attrib.get("duration", "00:00:00.0000000"), reverse=True)
sorted_by_outcome_then_duration = sorted(sorted_by_duration, key=lambda result: result.get("outcome") == "passed")
for result in sorted_by_outcome_then_duration:
    print(f'{result.attrib.get("duration")}s ({result.get("outcome")}) - {result.attrib.get("testName")}')