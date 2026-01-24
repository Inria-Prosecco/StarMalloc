#!/bin/bash
DATE=$(eval date)
DIR="bench/$DATE"
echo "Data will be saved in $DIR..."
mkdir -p "$DIR"
echo "Running the mimalloc-bench benchmarking suite..."
pushd extern/mimalloc-bench/out/bench
#time ../../bench.sh sys hm st cfrac no-security no-spec no-spec-bench no-linux -n=$@ 2>mimalloc-bench-errors.txt
#time ../../bench.sh sys hm st allt no-security no-spec no-spec-bench no-linux -n=$@ 2>mimalloc-bench-errors.txt
time ../../bench.sh sys hm st allt no-security no-spec no-spec-bench -n=$@ 2>mimalloc-bench-errors.txt
popd

cp extern/mimalloc-bench/out/bench/benchres.csv "$DIR/"
cp extern/mimalloc-bench/out/bench/mimalloc-bench-errors.txt "$DIR/"

echo "Generating PDF files corresponding to results..."
pushd "$DIR"
python "../tabs.py" benchres.csv $@
touch latex-log.txt
latexmk -pdf tabular-time.tex &>> latex-log.txt
latexmk -pdf tabular-rss.tex &>> latex-log.txt
popd
