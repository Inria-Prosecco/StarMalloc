#!/usr/bin/env python3
import argparse
from pathlib import Path

# timer
from tqdm import tqdm

# open compressed files
import lzma
# regexp
#import re

def create_arg_parser():
  parser = argparse.ArgumentParser(description="hwlogmalloc parser")
  parser.add_argument(
    "input_path",
    type=Path,             
    help="Path to the input file")
  #parser.add_argument('--outputDirectory',
  #                help='Path to the output that contains the resumes.')
  return parser

def magic_value(x: int):
  return 2**64 -x

def magic_value_bij(x: int):
  return -x + 2**64

# Assume: 2**64-n, where n is small, is never:
# - an integer/pointer argument to allocation/deallocation functions
# - an integer/pointer result of allocation/deallocation functions
# This is required, as tracing can sometimes fail and lead to ambiguous cases,
# thus, instead of using malloc=1, free=2, ...
# use malloc=magic_value(1), free=magic_value(2), ...

NB_FUNCTIONS = 2 # malloc, free, TODO
MAGIC_THRESHOLD = magic_value(NB_FUNCTIONS)

# malloc event is of the form:
# 1;<size>;<ptr>
# (3 ptwrite instructions)
# free event is of the form:
# 2;<ptr>
# (2 ptwrite instructions)

def parse(input_path, stop_at=0):
  with lzma.open(input_path, 'rt') as fd:
    #p1 = re.compile(r"\s+[a-zA-Z0-9_-]+\s+[0-9]+\s+[0-9]+\.[0-9]+")
    # exclude two first lines
    k = 0
    # per-thread information
    tid_map = {}
    errors = 0
    for line in tqdm(fd):
      parts = line.split(":")
      # not a log line
      if len(parts) < 5:
        #print(line)
        # RESET
        if tid in tid_map:
          tid_map[tid]["reset"] = 2 # hardcoded
        continue
      #if p1.match(parts[0]):
      #  print("OK")

      k += 1
      #print(k)
      if stop_at > 0 and k >= stop_at:
        break
      #if k <= 2:
      #  continue

      words = line.split(" ")
      words = list(filter(None, words))
      tid = words[1] # OK?
      payload = words[8]


      #words2 = line.split("payload: ")
      #payload = words2[1][:9]

      #print(line)
      #print(tid, payload)
      #print(k)
      #print(tid, int(payload, 16))
      if tid not in tid_map:
        print("New thread:", tid)
        tid_map[tid] = {}
        tid_map[tid]["status"] = 0
        tid_map[tid]["buffer"] = []
        tid_map[tid]["malloc"] = []
        tid_map[tid]["free"] = []
        tid_map[tid]["reset"] = False

      #print(k, line)

      payload_as_int = int(payload, 16)
      # traces can be malformed, thus giving the priority to the assumed
      # unambiguous beginning of one function execution
      if payload_as_int >= MAGIC_THRESHOLD:
        old_status = tid_map[tid]["status"]
        new_status = magic_value_bij(payload_as_int)
        tid_map[tid]["status"] = new_status
        tid_map[tid]["buffer"] = []
        if old_status != 0:
          #print("Incomplete tracing... interrupting function trace for another")
          errors += 1
          continue
      # continuing to parse a function trace
      else:
        status = tid_map[tid]["status"]
        buffer_len = len(tid_map[tid]["buffer"])
        if status == 0:
          #print("Incomplete tracing... skipping until next function trace")
          errors += 1
          continue
        elif status == 1:
          if buffer_len == 0:
            size = int(payload, 16)
            tid_map[tid]["buffer"].append(size)
          elif buffer_len == 1:
            #print("MALLOC", tid_map[tid]["buffer"])
            size = tid_map[tid]["buffer"][0]
            returned_ptr = payload
            tid_map[tid]["malloc"].append((size, returned_ptr))
            tid_map[tid]["buffer"] = []
            tid_map[tid]["status"] = 0
          else:
            raise ValueError("Malloc parsing: buffer too long")
        elif status == 2:
          if buffer_len == 0:
            given_ptr = payload
            tid_map[tid]["free"].append(given_ptr)
            tid_map[tid]["buffer"] = []
            tid_map[tid]["status"] = 0
          else:
            raise ValueError("Free parsing: buffer too long")
        else:
          raise ValueError("Undefined status 2", status)

  print ("# SUMMARY")
  print(k, "lines parsed:")
  print(errors, "errors (=", end="")
  print("%10.3E" % float(errors/k), end="")
  print("%)")
  for tid in tid_map:
    print("- Thread", tid)
    print("  - malloc: ", len(tid_map[tid]["malloc"]))
    print("  - free: ", len(tid_map[tid]["free"]))

if __name__ == "__main__":
  arg_parser = create_arg_parser()
  parsed_args = arg_parser.parse_args()
  p = parsed_args
  #print(p.input_path, type(p.input_path), p.input_path.exists())
  if p.input_path.exists():
    print("Parsing...")
    parse(p.input_path, 0)
  else:
    print("Input file does not exist.")
