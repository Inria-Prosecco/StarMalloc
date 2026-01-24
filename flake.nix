{
  description = "StarMalloc";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    fstar-src = {
      url = "github:FStarLang/FStar";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    steel-src = {
      url = "github:FStarLang/steel";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.flake-utils.follows = "fstar-src/flake-utils";
      inputs.fstar.follows = "fstar-src";
    };
    krml-src = {
      url = "github:FStarLang/karamel";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.flake-utils.follows = "fstar-src/flake-utils";
      inputs.fstar.follows = "fstar-src";
    };
    nix-mimalloc-bench = {
      url = "github:cmovcc/nix-mimalloc-bench";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = inputs@{self, nixpkgs, fstar-src, krml-src, steel-src, nix-mimalloc-bench}:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
      inherit (pkgs) lib;
      fstar-z3 = fstar-src.packages.${system}.z3;
      fstar = fstar-src.packages.${system}.fstar;
      steel = steel-src.packages.${system}.steel;
      karamel = krml-src.packages.${system}.karamel.home;

      # light build: no verification involved, only compile C files
      starmalloc-light = pkgs.stdenv.mkDerivation {
        name = "StarMalloc (light build)";
        src = lib.sourceByRegex ./. [
          "dist(/.*)?"
          "vendor(/.*)?"
          "c(/.*)?"
          "Makefile.include"
          "Makefile"
        ];
        enableParallelBuilding = true;
        buildInputs = [ ];
        # TODO: unaesthetic workaround, could this be improved?
        STEEL_HOME = 1;
        KRML_HOME = 1;
        # use vendored files so that Steel and KaRaMeL are not required
        VENDOR = 1;
        # skip F* dependency check so that F* is not required
        NODEPEND = 1;
        installPhase = "mkdir $out && cp -r dist out/*.so $out";
        buildFlags = [ "debug_light" "light" ];
      };

      # light build with whole repo as output 
      starmalloc-light-full-repo = starmalloc-light.overrideAttrs (finalAttrs: previousAttrs: {
        src = ./.;
        name = "StarMalloc (light build, full repo as output)";
        installPhase = "mkdir $out && cp -r * $out";
      });

      # full build: verify, extract and compile
      starmalloc = pkgs.stdenv.mkDerivation {
        name = "StarMalloc (full build)";
        src = lib.sourceByRegex ./. [
          "lib_avl_common(/.*)?"
          "lib_avl_mono(/.*)?"
          "lib_bitmap(/.*)?"
          "lib_list(/.*)?"
          "lib_misc(/.*)?"
          "src(/.*)?"
          "vendor(/.*)?"
          "c(/.*)?"
          "Makefile.include"
          "Makefile"
          "spdx-header.txt"
        ];
        enableParallelBuilding = true;
        buildInputs = [ fstar steel karamel ];
        STEEL_HOME = steel;
        KRML_HOME = karamel;
        installPhase = "mkdir $out && cp -r dist out/*.so $out";
        buildFlags = [ "debug_lib" "lib" ];
      };

      # check whether dist/ is up-to-date
      check-dist = pkgs.stdenv.mkDerivation {
        name = "StarMalloc (dist/ check)";
        src = lib.sourceByRegex ./. [
          "dist(/.*)?"
        ];
        buildInputs = [ starmalloc ];
        installPhase = ''
          if [[ -z $(diff -qr dist ${starmalloc}/dist) ]]; then
            mkdir $out
          else
            diff --color=always -Naur dist ${starmalloc}/dist
            exit 1
          fi
        '';
      };

      # check whether vendor/ is up-to-date
      check-vendor = pkgs.stdenv.mkDerivation {
        name = "StarMalloc (vendor/ check)";
        src = lib.sourceByRegex ./. [
          "vendor(/.*)?"
        ];
        buildInputs = [ steel karamel ];
        STEEL_HOME = steel;
        KRML_HOME = karamel;
        installPhase = ''
          # Steel
          mkdir -p temp_vendor/steel
          mkdir -p temp_vendor/steel/include
          cp -r $STEEL_HOME/include/steel/ temp_vendor/steel/include/steel/
          mkdir -p temp_vendor/steel/src
          cp -r $STEEL_HOME/src/c/ temp_vendor/steel/src/c/

          # KaRaMeL
          mkdir -p temp_vendor/karamel
          cp -r $KRML_HOME/include temp_vendor/karamel/include
          mkdir -p temp_vendor/karamel/krmllib/dist
          cp -r $KRML_HOME/krmllib/dist/minimal temp_vendor/karamel/krmllib/dist/minimal

          if [[ -z $(diff -qr vendor temp_vendor) ]]; then
            mkdir $out
          else
            diff --color=always -Naur vendor temp_vendor
            exit 1
          fi
        '';
      };

      # fast full build: extract and compile (verification is very light: SMT queries are admitted)
      starmalloc-admit-smt = starmalloc.overrideAttrs (finalAttrs: previousAttrs: {
        name = "StarMalloc (admit SMT queries build)";
        OTHERFLAGS = "--admit_smt_queries true";
      });

      # check whether verification is stable
      starmalloc-quake = starmalloc.overrideAttrs (finalAttrs: previousAttrs: {
        name = "StarMalloc (stability check build)";
        OTHERFLAGS = "--quake 5/5";
      });

      # mimalloc-bench
      mimalloc-bench = nix-mimalloc-bench.packages.${system}.bench-stage4;

      # Firefox
      firefox-unwrapped-no-mozjemalloc = ((pkgs.extend (self: super: {
        buildMozillaMach = opts: super.buildMozillaMach (opts // {
          extraConfigureFlags = [ "--disable-jemalloc" ];
        });
      })).firefox-unwrapped.override {
        pgoSupport = false; # reduce build time
        ltoSupport = false; # reduce peak RAM usage
      }).overrideAttrs (drv: {
        #patches = [];
      }) // {
        # confirmed using file descriptors-based logs that this is not needed
        #extraConfigureFlags = [ "--disable-jemalloc" ];
      };
      firefox-no-mozjemalloc = pkgs.wrapFirefox firefox-unwrapped-no-mozjemalloc {};

    in
    {
      packages.${system} = {
        inherit
          starmalloc-light
          starmalloc
          starmalloc-admit-smt starmalloc-quake
          check-dist check-vendor
          mimalloc-bench
          #add-mimalloc-bench-to-tree
          firefox-unwrapped-no-mozjemalloc
          firefox-no-mozjemalloc;
        default=starmalloc;
      };
      devShells.${system}.default = pkgs.mkShell {
        #buildInputs = with pkgs; [
        #];
        packages = with pkgs; [
          # verification software
          fstar-z3 fstar steel karamel
          # benchmarks: mimalloc-bench
          util-linux bash time
          readline #lua
          bc #redis
          ghostscript_headless #gs
          ruby #rbstress
          z3 #z3
          cmake gmp #lean
          flex bison #linux
          # benchmarks: mimalloc-bench results
          python3
          python3Packages.scipy
          (texlive.combine {
            inherit (texlive) scheme-small latexmk;
          })
          # benchmarks: Firefox
          #firefox-no-mozjemalloc
        ];
        shellHook = ''
          mkdir -p extern
          cp -r ${mimalloc-bench} extern/mimalloc-bench
          chmod -R +w extern/mimalloc-bench
          mkdir -p extern/mimalloc-bench/extern/st
          cp out/starmalloc.so extern/mimalloc-bench/extern/st
          # add StarMalloc to the list of all allocators, using the st abbreviation
          sed -i 's/readonly alloc_all="sys/readonly alloc_all="sys st/' extern/mimalloc-bench/bench.sh
          # add StarMalloc to the list of all allocators paths, using the st abbreviation
          sed -i 's/readonly lib_tbb_dir="$(dirname $lib_tbb)"/readonly lib_tbb_dir="$(dirname $lib_tbb)"\nalloc_lib_add "st" "$localdevdir\/st\/starmalloc.so"\n/' extern/mimalloc-bench/bench.sh
          # tests_all3 and tests_all4 should also be run when using the allt abbreviation
          sed -i 's/tests_allt="$tests_all1 $tests_all2"/tests_allt="$tests_all1 $tests_all2 $tests_all3 $tests_all4"/' extern/mimalloc-bench/bench.sh
          # lean and lean-mathlib should not be excluded
          sed -i 's/tests_exclude="$tests_exclude lean lean-mathlib"/tests_exclude="$tests_exclude"/' extern/mimalloc-bench/bench.sh
          # CMake issue workaround
          mkdir -p extern/mimalloc-bench/extern/lean/out/release
          pushd extern/mimalloc-bench/extern/lean/out/release
          cmake ../../src -DCMAKE_POLICY_VERSION_MINIMUM=3.5 -DCUSTOM_ALLOCATORS=OFF -DLEAN_EXTRA_CXX_FLAGS="-w"
          popd
          # TODO: other fixes?
        '';
        STEEL_HOME = steel;
        KRML_HOME = karamel;
        NIX_CFLAGS_COMPILE="-std=gnu11 -Wno-implicit-function-declaration -Wno-int-conversion"; #linux bench
      };
    };
}
