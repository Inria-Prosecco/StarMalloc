#!/bin/bash
set -euo pipefail
readonly PROGNAME=$(basename $0)

# TODO:
# - add an option to update everything

OTHERFLAGS=${OTHERFLAGS:=""}
CORES=${CORES:=$(nproc)}

setup() {
  echo "0. Setup"

  if [[ -z "$(which z3 2>/dev/null)" ]]; then
  echo "z3 is not in the PATH, exiting"
  	exit 1
  fi

  if [[ -z "${FSTAR_HOME}" ]]; then
  	echo "FSTAR_HOME env var is not set, exiting"
  	exit 1
  fi

  if [[ -z "${STEEL_HOME}" ]]; then
  	echo "STEEL_HOME env var is not set, exiting"
  	exit 1
  fi

  if [[ -z "${KRML_HOME}" ]]; then
  	echo "KRML_HOME env var is not set, exiting"
  	exit 1
  fi
  echo "z3 is in the PATH, {FSTAR,STEEL,KRML}_HOME are set"

  if [[ -z "$(which dpkg-query 2>/dev/null)" ]]; then
  	echo "dpkg-query is not in the PATH, skipping checks"
  else
    echo "Dependencies check using dpkg-query..."
    dpkg-query -s \
      g++ clang lld llvm-dev unzip \
      dos2unix linuxinfo bc libgmp-dev wget \
      cmake python3 ruby ninja-build libtool \
      autoconf sed ghostscript time curl \
      automake libatomic1 libgflags-dev libsnappy-dev zlib1g-dev \
      libbz2-dev liblz4-dev libzstd-dev libreadline-dev \
      gawk bazel-bootstrap 1>/dev/null
      #last line = missing for tcg/pa
    echo "Required Debian packages are installed"
  fi
}

build_starmalloc() {
  echo "1. Build StarMalloc"
  #echo "1.a clone StarMalloc"
  #if [[ -d "StarMalloc" ]]; then
  #	echo "StarMalloc repo has already been cloned, skipping"
  #else
  #	git clone git@github.com:Inria-Prosecco/StarMalloc.git
  #fi

  echo "1.b build StarMalloc"
  if [[ -f "StarMalloc/out/h_starmalloc.so" ]]; then
  	echo "StarMalloc lib is already built, skipping"
  else
  	echo OTHERFLAGS=\"$OTHERFLAGS\" make lib hardened_lib -j $CORES
  	OTHERFLAGS=$OTHERFLAGS make lib hardened_lib -j $CORES
  fi
}

build_mimalloc_bench() {
  echo "2. Build mimalloc-bench"

  echo "2.a clone mimalloc-bench"
  if [[ -d "extern/mimalloc-bench" ]]; then
  	echo "mimalloc-bench repo has already been cloned, skipping"
  else
    mkdir -p extern
    pushd extern 1>/dev/null
  	git clone https://github.com/daanx/mimalloc-bench
    popd 1>/dev/null
  fi

  echo "2.b build allocators to be benched"
  pushd extern/mimalloc-bench 1>/dev/null
  #TODO: fix pa + tcg
  bash build-bench-env.sh all no-pa no-tcg no-packages
  popd 1>/dev/null
}

apply_starmalloc_tweak() {
  echo "3. StarMalloc tweak: \
    install StarMalloc libs within mimalloc-bench dir"
  pushd extern/mimalloc-bench 1>/dev/null
  mkdir -p extern/st
  cp out/*.so extern/st
  if [[ -f "../mb-tweak-starmalloc.txt" ]]; then
  	echo "StarMalloc tweak already applied to mimalloc-bench"
  else
  	# add StarMalloc to the list of all allocators, using the st abbreviation
  	sed -i 's/readonly alloc_all="sys/readonly alloc_all="sys st/' bench.sh
  	# add StarMalloc to the list of all allocators paths, using the st abbreviation
  	sed -i 's/readonly lib_tbb_dir="$(dirname $lib_tbb)"/readonly lib_tbb_dir="$(dirname $lib_tbb)"\nalloc_lib_add "st" "$localdevdir\/st\/h_starmalloc.so"\n/' bench.sh
  	touch ../mb-tweak-starmalloc.txt
  fi
  popd 1>/dev/null
}

apply_mimalloc_bench_tweak() {
  echo "4. Mimalloc-bench tweak:\
    fix mimalloc-bench, allt should run all tests"
  pushd extern/mimalloc-bench 1>/dev/null
  if [[ -f "../mb-tweak-allt.txt" ]]; then
  	echo "Allt tweak already applied to mimalloc-bench/"
  else
  	# tests_all3 and tests_all4 should also be run when using the allt abbreviation
  	sed -i 's/tests_allt="$tests_all1 $tests_all2"/tests_allt="$tests_all1 $tests_all2 $tests_all3 $tests_all4"/' bench.sh
  	# lean and lean-mathlib should not be excluded
  	sed -i 's/tests_exclude="$tests_exclude lean lean-mathlib"/tests_exclude="$tests_exclude"/' bench.sh
  	touch ../mb-tweak-allt.txt
  fi
  popd 1>/dev/null
}

usage() {
  cat <<-EOF
  usage: [...] $PROGNAME options

  As part of the StarMalloc repository,
  this script builds StarMalloc and mimalloc-bench,
  patches the latter to add StarMalloc support and
  to use all benches when specified so (allt).

  OPTIONS:
    -h --help show this help

  This script assumes that:
  - the z3+F*+Steel+KaRaMeL toolchain has been set up
  (StarMalloc build);
  - mimalloc-bench dependencies have been installed
  (mimalloc-bench build).

  Environment variables usage for the Starmalloc build:
  - CORES: specify number of jobs
  (e.g. CORES=1 bash $PROGNAME);
  - OTHERFLAGS: specify additional F* options
  (e.g. OTHERFLAGS="--admit_smt_queries true" bash $PROGNAME).
EOF
}

main() {
  setup
  build_starmalloc
  build_mimalloc_bench
  apply_starmalloc_tweak
  apply_mimalloc_bench_tweak
}

readonly ARGS=${1:-""}

if test "$ARGS" = "-h"; then
  usage
else
  main

  cat <<-EOF
  Now, everything is ready to bench StarMalloc wrt to other allocators,
  using mimalloc-bench.
  From the mimalloc-bench/out/bench directory,
  you can use the following command:
  bash ../../bench.sh \$ALLOCATORS \$BENCHES,
  e.g.
  bash ../../bench.sh sys mi hm st allt.
EOF

fi
