#!/usr/bin/env python3
import argparse
from pathlib import Path

# open compressed files
import lzma
# regexp
import re

def create_arg_parser():
  parser = argparse.ArgumentParser(description="hwlogmalloc parser")
  parser.add_argument(
    "input_path",
    type=Path,             
    help="Path to the input file")
  #parser.add_argument('--outputDirectory',
  #                help='Path to the output that contains the resumes.')
  return parser

def parse(input_path):
  with lzma.open(input_path, 'rt') as fd:
    # exclude two first lines
    k = 0
    # per-thread information
    tid_map = {}
    for line in fd:
      #k += 1
      #if k <= 2:
      #  continue

      words = line.split(" ")
      words = list(filter(None, words))
      tid = words[1] # OK?
      payload = words[8]

      #words2 = line.split("payload: ")
      #payload = words2[1][:9]

      print(tid, payload)
      #print(tid, int(payload, 16))
      if tid not in tid_map:
        tid_map[tid] = {}
        tid_map[tid]["b"] = False

if __name__ == "__main__":
  arg_parser = create_arg_parser()
  parsed_args = arg_parser.parse_args()
  p = parsed_args
  #print(p.input_path, type(p.input_path), p.input_path.exists())
  if p.input_path.exists():
    print("Parsing...")
    parse(p.input_path)
  else:
    print("Input file does not exist.")
