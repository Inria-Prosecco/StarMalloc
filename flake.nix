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
  };

  outputs = inputs@{self, nixpkgs, fstar-src, krml-src, steel-src}:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
      inherit (pkgs) lib;
      z3 = fstar-src.packages.${system}.z3;
      fstar = fstar-src.packages.${system}.fstar;
      steel = steel-src.packages.${system}.steel;
      karamel = krml-src.packages.${system}.karamel.home;

      # allocator derivations
      # TODO: use pkgs.llvmPackages_latest.stdenv.mkDerivation
      # currently, there is some linking issue, try to fix it/report it

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
        FSTAR_HOME = 1;
        STEEL_HOME = 1;
        KRML_HOME = 1;
        # use vendored files, as this would require Steel and KaRaMeL
        VENDOR = 1;
        # skip F* dependency check, as this would require F*
        NODEPEND = 1;
        installPhase = "mkdir $out && cp -r dist out/*.so $out";
        buildFlags = [ "debug_light" "light" ];
      };

      # full build: verify, extract and compile
      starmalloc = pkgs.stdenv.mkDerivation {
        name = "StarMalloc (full build)";
        src = lib.sourceByRegex ./. [
          "lib_avl_common(/.*)?"
          "lib_avl_mono(/.*)?"
          "lib_bitmap(/.*)?"
          "lib_list(/.*)?"
          "lib_misc(/.*)?"
          "lib_ringbuffer(/.*)?"
          "src(/.*)?"
          "c(/.*)?"
          "Makefile.include"
          "Makefile"
          "spdx-header.txt"
        ];
        enableParallelBuilding = true;
        buildInputs = [ fstar steel karamel pkgs.removeReferencesTo ];
        FSTAR_HOME = fstar;
        STEEL_HOME = steel;
        KRML_HOME = karamel;
        installPhase = "mkdir $out && cp -r dist out/*.so $out";
        buildFlags = [ "debug_lib" "lib" ];
        postInstall = ''
          find dist -type f -name "*" -exec remove-references-to -t ${karamel} {} \;
        '';
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
      # check that build is stable
      starmalloc-quake = starmalloc.overrideAttrs (finalAttrs: previousAttrs: {
        name = "StarMalloc (stability check build)";
        OTHERFLAGS = "--quake 5/5";
      });
    in
    {
      packages.${system} = {
        inherit starmalloc-light starmalloc starmalloc-admit-smt starmalloc-quake check-dist check-vendor;
        default=starmalloc;
      };
    };
}
