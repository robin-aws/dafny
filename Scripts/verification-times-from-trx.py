#!/usr/bin/env python3
 
import xml.etree.ElementTree as ET
import sys

root = ET.parse(sys.argv[1]).getroot()
results = root.find("./{http://microsoft.com/schemas/VisualStudio/TeamTest/2010}Results")
sorted_by_duration = sorted(results, key=lambda result: result.attrib.get("duration", "00:00:00.0000000"), reverse=True)
sorted_by_outcome_then_duration = sorted(sorted_by_duration, key=lambda result: result.attrib["outcome"] == "passed")
for result in sorted_by_outcome_then_duration:
    print(f'{result.attrib["duration"]}s ({result.attrib["outcome"]}) - {result.attrib["testName"]}')
